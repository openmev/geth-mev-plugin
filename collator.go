package main

import (
	"errors"
	"math/big"
	"sort"
	"sync"
	"time"
	"fmt"
	"context"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/miner"
)

var (
	errInterrupted = errors.New("work-cycle interrupted by miner: new head block received")
)

type MevCollator struct {
	maxMergedBundles uint
	bundleMu         sync.Mutex
	bundles          []MevBundle
	workers          []bundleWorker
	pool             miner.Pool
	exitCh chan struct{}

	commitMu sync.Mutex
	// these values are used per-work-cycle
	lastParentHash common.Hash
	bestProfit *big.Int
}

type MevBundle struct {
	Transactions      types.Transactions
	BlockNumber       *big.Int
	MinTimestamp      uint64
	MaxTimestamp      uint64
	RevertingTxHashes []common.Hash
}

type simulatedBundle struct {
	mevGasPrice       *big.Int
	totalEth          *big.Int
	ethSentToCoinbase *big.Int
	totalGasUsed      uint64
	originalBundle    MevBundle
}

type bundlerWork struct {
	work miner.BlockCollatorWork
	simulatedBundles []simulatedBundle
}

type bundleWorker struct {
	id               int
	exitCh           chan struct{}
	newWorkCh        chan bundlerWork
	maxMergedBundles uint
	pool             miner.Pool
}

func containsHash(arr []common.Hash, match common.Hash) bool {
	for _, elem := range arr {
		if elem == match {
			return true
		}
	}
	return false
}

var (
	ErrBundleTxReverted = errors.New("bundle tx was reverted (not in allowed reverted list)")
)

// eligibleBundles returns a list of bundles valid for the given blockNumber/blockTimestamp
// also prunes bundles that are outdated
func (c *MevCollator) eligibleBundles(blockNumber *big.Int, blockTimestamp uint64) []MevBundle {
	c.bundleMu.Lock()
	defer c.bundleMu.Unlock()

	// returned values
	var ret []MevBundle
	// rolled over values
	var bundles []MevBundle

	for _, bundle := range c.bundles {
		// Prune outdated bundles
		if (bundle.MaxTimestamp != 0 && blockTimestamp > bundle.MaxTimestamp) || blockNumber.Cmp(bundle.BlockNumber) > 0 {
			continue
		}

		// Roll over future bundles
		if (bundle.MinTimestamp != 0 && blockTimestamp < bundle.MinTimestamp) || blockNumber.Cmp(bundle.BlockNumber) < 0 {
			bundles = append(bundles, bundle)
			continue
		}

		// return the ones which are in time
		ret = append(ret, bundle)
		// keep the bundles around internally until they need to be pruned
		bundles = append(bundles, bundle)
	}

	c.bundles = bundles
	return ret
}

func computeBundleGas(bundle MevBundle, bs miner.BlockState, pendingTxs map[common.Address]types.Transactions) (simulatedBundle, error) {
	state := bs.State()
	header := bs.Header()
	signer := bs.Signer()

	var totalGasUsed uint64 = 0
	gasFees := new(big.Int)
	ethSentToCoinbase := new(big.Int)

	for _, tx := range bundle.Transactions {
		coinbaseBalanceBefore := state.GetBalance(bs.Etherbase())

		err, receipts := bs.AddTransactions(types.Transactions{tx})
		if err != nil && (errors.Is(err, miner.ErrInterruptRecommit) || errors.Is(err, miner.ErrInterruptRecommit)) {
			return simulatedBundle{}, err
		}
		if receipts[0].Status == types.ReceiptStatusFailed && !containsHash(bundle.RevertingTxHashes, receipts[0].TxHash) {
			return simulatedBundle{}, ErrBundleTxReverted
		}
		totalGasUsed += receipts[0].GasUsed

		from, err := types.Sender(signer, tx)
		if err != nil {
			return simulatedBundle{}, err
		}
		txInPendingPool := false
		if accountTxs, ok := pendingTxs[from]; ok {
			// check if tx is in pending pool
			txNonce := tx.Nonce()

			for _, accountTx := range accountTxs {
				if accountTx.Nonce() == txNonce {
					txInPendingPool = true
					break
				}
			}
		}
		gasUsed := new(big.Int).SetUint64(receipts[0].GasUsed)
		gasPrice, err := tx.EffectiveGasTip(header.BaseFee)
		if err != nil {
			return simulatedBundle{}, err
		}
		gasFeesTx := gasUsed.Mul(gasUsed, gasPrice)
		coinbaseBalanceAfter := state.GetBalance(bs.Etherbase())
		coinbaseDelta := big.NewInt(0).Sub(coinbaseBalanceAfter, coinbaseBalanceBefore)
		coinbaseDelta.Sub(coinbaseDelta, gasFeesTx)
		ethSentToCoinbase.Add(ethSentToCoinbase, coinbaseDelta)

		if !txInPendingPool {
			// If tx is not in pending pool, count the gas fees
			gasFees.Add(gasFees, gasFeesTx)
		}
	}
	totalEth := new(big.Int).Add(ethSentToCoinbase, gasFees)

	return simulatedBundle{
		mevGasPrice:       new(big.Int).Div(totalEth, new(big.Int).SetUint64(totalGasUsed)),
		totalEth:          totalEth,
		ethSentToCoinbase: ethSentToCoinbase,
		totalGasUsed:      totalGasUsed,
		originalBundle:    bundle,
	}, nil
}

// fill the block with as many bundles as the worker can add
// return the BlockState
func mergeBundles(work bundlerWork, pendingTxs map[common.Address]types.Transactions, locals []common.Address) (miner.BlockState, uint, uint, *big.Int, *big.Int, error) {
	bs := work.blockState
	if len(work.simulatedBundles) == 0 {
		return bs, 0, 0, big.NewInt(0), big.NewInt(0), nil
	}

	beforeBs := bs.Copy()
	resultBs := bs

	totalEth := big.NewInt(0)
	ethSentToCoinbase := big.NewInt(0)
	var numMergedBundles uint = 0
	var numTxs uint = 0

	for _, bundle := range work.simulatedBundles {
		// the floor gas price is 99/100 what was simulated at the top of the block
		floorGasPrice := new(big.Int).Mul(bundle.mevGasPrice, big.NewInt(99))
		floorGasPrice = floorGasPrice.Div(floorGasPrice, big.NewInt(100))

		simmed, err := computeBundleGas(bundle.originalBundle, resultBs, pendingTxs)
		if err != nil {
			if errors.Is(err, miner.ErrInterruptRecommit) || errors.Is(err, miner.ErrInterruptNewHead) {
				return nil, 0, 0, nil, nil, err
			} else {
				beforeBs = resultBs.Copy()
				continue
			}
		} else if simmed.mevGasPrice.Cmp(floorGasPrice) <= 0 {
			resultBs = beforeBs.Copy()
			continue
		}

		numTxs += uint(len(simmed.originalBundle.Transactions))

		totalEth.Add(totalEth, simmed.totalEth)
		ethSentToCoinbase.Add(ethSentToCoinbase, simmed.ethSentToCoinbase)
		numMergedBundles++
		if numMergedBundles >= work.maxMergedBundles {
			break
		}
	}

	return resultBs, numMergedBundles, numTxs, totalEth, ethSentToCoinbase, nil
}

func submitTransactions(ctx context.Context, bs BlockState, txs *types.TransactionsByPriceAndNonce, timer *time.Timer) bool {
	header := bs.Header()
	availableGas := header.GasLimit
	for {
		select {
		case <-ctx.Done():
			return true
		default:
		}

		if timer != nil {
			select {
			case <-timer.C:
				return false
			default:
			}
		}

		// Retrieve the next transaction and abort if all done
		tx := txs.Peek()
		if tx == nil {
			break
		}
		// Enough space for this tx?
		if availableGas < tx.Gas() {
			txs.Pop()
			continue
		}
		from, _ := types.Sender(bs.Signer(), tx)

		err, receipts := bs.AddTransactions(types.Transactions{tx})
		switch {
		case errors.Is(err, ErrGasLimitReached):
			// Pop the current out-of-gas transaction without shifting in the next from the account
			log.Trace("Gas limit exceeded for current block", "sender", from)
			txs.Pop()

		case errors.Is(err, ErrNonceTooLow):
			// New head notification data race between the transaction pool and miner, shift
			log.Trace("Skipping transaction with low nonce", "sender", from, "nonce", tx.Nonce())
			txs.Shift()

		case errors.Is(err, ErrNonceTooHigh):
			// Reorg notification data race between the transaction pool and miner, skip account =
			log.Trace("Skipping account with high nonce", "sender", from, "nonce", tx.Nonce())
			txs.Pop()

		case errors.Is(err, nil):
			availableGas = header.GasLimit - receipts[0].CumulativeGasUsed
			// Everything ok, collect the logs and shift in the next transaction from the same account
			txs.Shift()

		case errors.Is(err, ErrTxTypeNotSupported):
			// Pop the unsupported transaction without shifting in the next from the account
			log.Trace("Skipping unsupported transaction type", "sender", from, "type", tx.Type())
			txs.Pop()
		default:
			// Strange error, discard the transaction and get the next in line (note, the
			// nonce-too-high clause will prevent us from executing in vain).
			log.Debug("Transaction failed, account skipped", "hash", tx.Hash(), "err", err)
			txs.Shift()
		}
	}

	return false
}

func (c *bundleWorker) fillTransactions(ctx context.Context, bs BlockState, timer *time.Timer) {
        header := bs.Header()
        txs, err := c.pool.Pending(true)
        if err != nil {
                log.Error("could not get pending transactions from the pool", "err", err)
                return
        }
        if len(txs) == 0 {
                return
        }
        // Split the pending transactions into locals and remotes
        localTxs, remoteTxs := make(map[common.Address]types.Transactions), txs
        for _, account := range c.pool.Locals() {
                if accountTxs := remoteTxs[account]; len(accountTxs) > 0 {
                        delete(remoteTxs, account)
                        localTxs[account] = accountTxs
                }
        }
        if len(localTxs) > 0 {
                if submitTransactions(ctx, bs, types.NewTransactionsByPriceAndNonce(bs.Signer(), localTxs, header.BaseFee), timer) {
                        return
                }
        }
        if len(remoteTxs) > 0 {
                if submitTransactions(ctx, bs, types.NewTransactionsByPriceAndNonce(bs.Signer(), remoteTxs, header.BaseFee), timer) {
                        return
                }
        }
}

func (w *bundleWorker) workerMainLoop() {
	for {
		select {
		case work := <-w.newWorkCh:
			pendingTxs, _ := w.collator.pool.Pending(true)
			locals := w.collator.pool.Locals()

			bs, numTxs, numBundles, totalEth, profit, err := mergeBundles(work, pendingTxs, locals)
			if err != nil {
				continue
			}
			_ = totalEth

			if numTxs == 0 && w.maxMergedBundles != 0 {
				continue
			}

			if w.maxMergedBundles != 0 && numBundles != w.maxMergedBundles {
				continue
			}

			if numTxs == 0 && len(pendingTxs) == 0 {
				continue
			}

			// TODO add tx-fees to profit
			if !fillTransactions(work.work.Block, pendingTxs, locals) {
				continue
			}

			log.Info(fmt.Sprintf("%d: evaluating block", c.id))

			header := work.work.Block.Header()

			w.collator.commitMu.Lock()

			// don't commit if the block is stale or the task doesn't increase profit
			if profit.Cmp(w.collator.bestProfit) < 0 || w.collator.lastParentHash != header.ParentHash {
				w.collator.commitMu.Unlock()
				continue
			}
			w.collator.bestProfit.Set(profit)
			w.collator.lastParentHash = header.ParentHash
			log.Info("collator called Commit")
			bs.Commit()
			work.commitMu.Unlock()
		case <-c.exitCh:
			return
		}
	}
}

func simulateBundles(work miner.BlockCollatorWork, b []MevBundle, pendingTxs map[common.Address]types.Transactions, locals []common.Address) ([]simulatedBundle, error) {
	result := []simulatedBundle{}

	if len(b) == 0 {
		return []simulatedBundle{}, nil
	}

	bsBefore := bs.Copy()

	for _, bundle := range b {
		simulated, err := computeBundleGas(bundle, bsBefore, pendingTxs)
		bsBefore = bs.Copy()
		if err != nil {
			if errors.Is(errInterrupted, err) {
				return nil, err
			} else {
				log.Error("failed to simulate bndle", "err", err)
				continue
			}
		}
		result = append(result, simulated)
	}
	return result, nil
}

func (c *MevCollator) collateBlock(work miner.BlockCollatorWork) {
	header := bs.Header()
	bundles := c.eligibleBundles(header.Number, header.Time)

	var bundleBlocksExpected uint
	var wg sync.WaitGroup
	bestProfit := big.NewInt(0)
	commitMu := sync.Mutex{}

	pendingTxs, _ := c.pool.Pending(true)
	locals := c.pool.Locals()

	blockCopy := work.Block.Copy()
	// signal to our "normal" worker to start building a block using the standard strategy
	c.workers[0].newWorkCh <- bundlerWork{work: work, simulatedBundles: nil}

	if len(bundles) > 0 {
		var bundleBlocksExpected uint
		if len(bundles) > int(c.maxMergedBundles) {
			bundleBlocksExpected = c.maxMergedBundles
		} else {
			bundleBlocksExpected = uint(len(bundles))
		}

		simulatedBundles := simulateBundles(blockCopy.Copy(), bundles, pendingTxs, locals)
		sort.SliceStable(simulatedBundles, func(i, j int) bool {
			return simulatedBundles[j].mevGasPrice.Cmp(simulatedBundles[i].mevGasPrice) < 0
		})

		for i := 0; i < int(bundleBlocksExpected); i++ {
			c.workers[i+1].newWorkCh <- bundlerWork{work: miner.BlockCollatorWork{block: blockCopy(), ctx: work.Ctx},  simulatedBundles: simulatedBundles}
		}
	}
}

func (c *MevCollator) CollateBlock(bs BlockState, pool Pool) {
	panic("pls implement me")
}

func (c *MevCollator) CollateBlocks(miner MinerState, pool Pool, blockCh <-chan BlockCollatorWork, exitCh <-chan struct{}) {
	c.pool = pool
	for i := 0; i < int(c.maxMergedBundles); i++ {
		worker := bundleWorker{
			collator: c,
			exitCh:           c.closeCh,
			newWorkCh:        make(chan bundlerWork),
			maxMergedBundles: uint(i),
			id:               i,
		}

		c.workers = append(c.workers, worker)
		go worker.workerMainLoop()
	}

	for {
		select {
		case work := blockCh:
			// TODO implement recommit mechanism
			c.CollateBlock(work.Ctx, work.Block)
		case <-exitCh:
			// TODO close all workers
		}
	}
}
