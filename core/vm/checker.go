// TODO: Shelly - add relevant copyright notices

package vm

import (
	"database/sql"
	"fmt"
	"math/big"
	"os"
	"strconv"
	"time"

	"sync"

	"github.com/ethereum/go-ethereum/common"
	GenStack "github.com/golang-collections/collections/stack"
	set "gopkg.in/fatih/set.v0"
)

var DISABLE_CHECKER = false
var INCLUDE_WW_CONFLICTS = false

var debugLevel = 0

// ImportantDebug will always print an output to stdout
func ImportantDebug(format string, a ...interface{}) (n int, err error) {
	return Debug(0, format, a...)
}

// Debug prints a debug line depending on how the program was compiled and on the severity (=level) of the debug
func Debug(level int, format string, a ...interface{}) (n int, err error) {
	if level == 0 || level <= debugLevel {
		return fmt.Printf(format+"\n", a...)
	}

	return 0, nil
}

// TheChecker is used by EVM
var theChecker *Checker
var once sync.Once

// TheChecker is for singleton implementation
func TheChecker() *Checker {
	once.Do(func() {
		theChecker = &Checker{}
		theChecker.initChecker()
	})

	return theChecker
}

// Segment is the type for non interrupted traces
type Segment struct {
	contract           common.Address
	depth              int
	prevSegment        *Segment
	indexInTransaction int
	indexInCall        int
	readSet            set.Interface // A set of all read-from locations
	writeSet           set.Interface // A set of all written-to locations
	invIdx			   int // The index of the starting segment of the invocation in which this segment appears

	// For ECF check only: may we ignore the segment?
	mayIgnore	bool

	// For starting segments only - how many segments the invocation it represents has
	invocationSize int
}

func (s *Segment) String() string {
	return fmt.Sprintf("{C=%v D=%v It=%v Ic=%v Inv=%v RS=%v WS=%v, Ig=%v}", s.contract.Hex(), s.depth, s.indexInTransaction, s.indexInCall, s.invIdx, s.readSet.String(), s.writeSet.String(), s.mayIgnore)
}

// Checker is the type of the to-be-generic checker - it is loaded with execution specific metadata but also global data for checker functionality
type Checker struct {
	transactionSegments []*Segment
	invocations         map[int][]*Segment // Maintains all segments pertaining to invocations in a certain depth: map from depth to all segments in that depth
	invocationsRanges	map[int]int // Map invocation start segment index to invocation end segment index
	runningSegments     *GenStack.Stack

	isRealCall bool
	evmStack   *GenStack.Stack

	TransactionID int
	origin        *common.Address
	blockNumber   *big.Int
	time          *big.Int

	processTime time.Time

	// Persistent part
	// DB Handler
	dbHandler *sql.DB

	numOfTransactionsCheckedSoFar int
}

// SetDbHandler allows to set the db handler from anywhere
func (checker *Checker) SetDbHandler(db *sql.DB) {
	checker.dbHandler = db
}

func (checker *Checker) initChecker() {
	checker.evmStack = GenStack.New()
	checker.runningSegments = GenStack.New()

	DISABLE_CHECKER = os.Getenv("EVM_DISABLE_ECF_CHECK") == "1"
	ImportantDebug("Disable ECF Checker is set to: %v", DISABLE_CHECKER)
	if DISABLE_CHECKER {
		ImportantDebug("ECF Check is DISABLED!")
	} else {
		ImportantDebug("ECF Check is in place!")
	}

	INCLUDE_WW_CONFLICTS = os.Getenv("EVM_ECF_CHECK_INCLUDE_WW_CONFLICTS") == "1"
	ImportantDebug("Including write-write conflicts: %v", INCLUDE_WW_CONFLICTS)

	debugLevelStr := os.Getenv("EVM_MONITOR_DEBUG_LEVEL")
	if debugLevelStr != "" {
		ImportantDebug("Debug level set to %s", debugLevelStr)
		debugLevelInt, _ := strconv.Atoi(debugLevelStr)
		debugLevel = debugLevelInt
	}
}

func (checker *Checker) GetLastSegment() *Segment {
	return checker.transactionSegments[len(checker.transactionSegments)-1]
}

func (checker *Checker) PushNewSegmentFromStart(contract *Contract) {
	segment := Segment{}
	if checker.runningSegments.Len() == 0 {
		segment = Segment{contract: contract.Address(),
			depth:              1,
			prevSegment:        nil,
			readSet:            set.New(),
			writeSet:           set.New(),
			indexInTransaction: 0,
			indexInCall:        0,
			invIdx:				0,
			mayIgnore:			false,
			invocationSize:     0}
		// Initializations
		checker.transactionSegments = make([]*Segment, 0)
		checker.invocations = make(map[int][]*Segment)
		checker.invocationsRanges = make(map[int]int)
	} else {
		segment = Segment{contract: contract.Address(),
			depth:              checker.GetLastSegment().depth + 1,
			prevSegment:        checker.GetLastSegment(),
			readSet:            set.New(),
			writeSet:           set.New(),
			indexInTransaction: checker.GetLastSegment().indexInTransaction+1,
			indexInCall:        0,
			invIdx:				checker.GetLastSegment().indexInTransaction+1,
			mayIgnore:			false,
			invocationSize:     0}
	}

	Debug(3, "Adding segment %v, also to running segments stack. EVM stack %v (%v), isRealCall %v", segment, checker.evmStack, checker.evmStack.Len(), checker.isRealCall)

	checker.transactionSegments = append(checker.transactionSegments, &segment)
	checker.runningSegments.Push(&segment)

	// Update invocations:
	if len(checker.invocations[segment.depth]) == 0 {
		checker.invocations[segment.depth] = make([]*Segment, 0)
	}

	checker.invocations[segment.depth] = append(checker.invocations[segment.depth], &segment)

	// Setting invocation range tentatively as current id
	checker.invocationsRanges[segment.indexInTransaction] = segment.indexInTransaction
}

func (checker *Checker) PushNewSegmentFromEnd() {
	(checker.runningSegments.Peek()).(*Segment).invocationSize++

	segment := Segment{contract: (checker.runningSegments.Peek()).(*Segment).contract,
		depth:              (checker.runningSegments.Peek()).(*Segment).depth,
		prevSegment:        checker.GetLastSegment(),
		readSet:            set.New(),
		writeSet:           set.New(),
		indexInTransaction: checker.GetLastSegment().indexInTransaction+1,
		indexInCall:        (checker.runningSegments.Peek()).(*Segment).invocationSize,
		mayIgnore:			false}

	Debug(3, "Adding segment %v", segment)

	checker.invocations[segment.depth] = append(checker.invocations[segment.depth], &segment)
	// Find starting segment from invocations map:
	for i := len(checker.invocations[segment.depth])-1 ; i >= 0 ; i-- {
		if checker.invocations[segment.depth][i].indexInCall == 0 {
			segment.invIdx = checker.invocations[segment.depth][i].indexInTransaction
			// Tentative, until a later segment arrives or the invocation actually ends
			checker.invocationsRanges[segment.invIdx] = segment.indexInTransaction
		}
	}

	checker.transactionSegments = append(checker.transactionSegments, &segment)
}

func reportNonECF(contract string, depth int, idx int, traceLen int) {
	checker := TheChecker()

	ImportantDebug("Adding non ECF transaction %d, origin %s, block %d, time %d, contract %s, depth %d, idx %d, tx len %d", checker.TransactionID,
		checker.origin.Hex(),
		checker.blockNumber,
		checker.time,
		contract,
		depth,
		idx,
		traceLen)

	stmt := fmt.Sprintf("insert into NON_ECF_TRACE(id, origin, block, time, contract, depth, start_index, length) VALUES(%d, '%s', %d, %d, '%s', %d, %d, %d)",
		checker.TransactionID,
		checker.origin.Hex(),
		checker.blockNumber,
		checker.time,
		contract,
		depth,
		idx,
		traceLen)

	_, dberr := checker.dbHandler.Exec(stmt)
	if dberr != nil {
		ImportantDebug("Failed to execute %s, %v", stmt, dberr)
	}
}

func (checker *Checker) getPrefix(segment *Segment, invocation int) ([]*Segment) {
	prefix := make([]*Segment, 0)
	invocationDepth := checker.transactionSegments[invocation].depth
	for i := range checker.invocations[invocationDepth] {
		candidate := checker.invocations[invocationDepth][i]

		// take candidate segments that have the same invIdx as the invocation and are before the input segment
		if candidate.invIdx == invocation {
			if candidate.indexInTransaction < segment.indexInTransaction { // A candidate segment of the same invocation before the current segment is added
				prefix = append(prefix, candidate)
			} else { // Once we finished with the invocation segments after the input segment, stop
				break
			}
		}
	}

	return prefix
}

func (checker *Checker) getSuffix(segment *Segment, invocation int) ([]*Segment) {
	suffix := make([]*Segment, 0)
	invocationDepth := checker.transactionSegments[invocation].depth
	for i := range checker.invocations[invocationDepth] {
		candidate := checker.invocations[invocationDepth][i]

		if candidate.invIdx == invocation &&
			candidate.indexInTransaction > segment.indexInTransaction { // A candidate segment of the given invocation after the current segment is added
			suffix = append(suffix, candidate)
		}
	}

	return suffix
}

func (checker *Checker) getInvocationSegments(startSegment *Segment) ([]*Segment) {
	suffix := checker.getSuffix(startSegment, startSegment.invIdx)
	invocation := make([]*Segment,0)
	invocation = append(invocation, startSegment)
	invocation = append(invocation, suffix...)
	return invocation
}

type CommutativityMatrixKey struct {
	invocationIdx int
	segmentId int
}

type CommutativityMatrixValue struct {
	prefixCommute, suffixCommute bool
}

func (checker *Checker) markReadOnlyInvocations() {
	C := set.New() // Candidate invocation set
	for i := range checker.invocationsRanges {
		C.Add(i) // Add all starting indices of invocations as candidate read-only invocations
	}

	i := 0
	for {
		if i >= len(checker.transactionSegments) {
			break
		}

		s := checker.transactionSegments[i]
		if !s.writeSet.IsEmpty() {
			// Every invocation that contains s is not read only AND is pertaining to the contract executing s
			for j := range checker.invocationsRanges {
				if j <= s.indexInTransaction && checker.invocationsRanges[j] >= s.indexInTransaction && s.contract == checker.transactionSegments[j].contract {
					C.Remove(j)
				}

				if j > s.indexInTransaction {
					break
				}
			}
			// We can now jump to the next invocation - additional writing segments do not add new information
			i = checker.invocationsRanges[s.invIdx]+1
		} else {
			i++
		}
	}

	// Now mark segments that can be ignored using C
	i = 0
	for {
		if i >= len(checker.transactionSegments) {
			break
		}

		s := checker.transactionSegments[i]

		if C.Has(s.invIdx) {
			s.mayIgnore = true
		}
	}
}

func (checker *Checker) buildCommutativityMatrix(invocations set.Interface) (map[CommutativityMatrixKey]CommutativityMatrixValue, bool, string, int, int) {
	commuteMatrix := make(map[CommutativityMatrixKey]CommutativityMatrixValue)
	for i := range checker.transactionSegments {
		segment := checker.transactionSegments[i]
		if segment.mayIgnore {
			continue
		}

		for j := range invocations.List() {
			// Check if s and j is of the same contract, and are not of the same invocation j:
			if segment.contract != checker.transactionSegments[j].contract || segment.invIdx == j {
				continue
			}

			prefix := checker.getPrefix(segment, j)
			suffix := checker.getSuffix(segment, j)

			invIdx := 0
			if len(prefix) == 0 {
				invIdx = segment.indexInTransaction
			} else {
				invIdx = prefix[0].indexInTransaction
			}

			// Calculate for prefix, suffix the read set and write set
			prefixRS := set.New()
			suffixRS := set.New()
			prefixWS := set.New()
			suffixWS := set.New()
			for prefixIdx := range prefix {
				prefixRS.Merge(prefix[prefixIdx].readSet)
				prefixWS.Merge(prefix[prefixIdx].writeSet)
			}

			for suffixIdx := range suffix {
				suffixRS.Merge(suffix[suffixIdx].readSet)
				suffixWS.Merge(suffix[suffixIdx].writeSet)
			}

			// Check commutativity
			prefixCommute := (set.Intersection(segment.readSet, prefixWS)).IsEmpty() && (set.Intersection(segment.writeSet, prefixRS)).IsEmpty()
			suffixCommute := (set.Intersection(segment.readSet, suffixWS)).IsEmpty() && (set.Intersection(segment.writeSet, suffixRS)).IsEmpty()

			if INCLUDE_WW_CONFLICTS {
				prefixCommute = prefixCommute && (set.Intersection(segment.writeSet, prefixWS)).IsEmpty()
				suffixCommute = suffixCommute && (set.Intersection(segment.writeSet, suffixWS)).IsEmpty()
			}

			// No commutativity at all -> Not ECF
			if !prefixCommute && !suffixCommute {
				ImportantDebug("Not ECF - Invocation %v (contract %v), segment %v (contract %v) [RS: %v, WS: %v], prefix RS: %v, prefix WS: %v, suffix RS: %v, suffix WS: %v", j, checker.transactionSegments[j].contract.Hex(), i,  segment.contract.Hex(), segment.readSet, segment.writeSet, prefixRS, prefixWS, suffixRS, suffixWS)
				ImportantDebug("Debug info: Transaction: %v \n invocations: %v \n invocation ranges: %v", checker.transactionSegments, checker.invocations,checker.invocationsRanges) // TODO: make Debug(0,)
				return commuteMatrix, false, segment.contract.Hex(), segment.depth, segment.indexInTransaction
			}

			// Otherwise, update in commutativity matrix
			commuteMatrix[CommutativityMatrixKey{invIdx, segment.indexInTransaction}] = CommutativityMatrixValue{prefixCommute, suffixCommute}
		}
	}

	return commuteMatrix, true, "", 0, 0
}

type IOCRelationKey struct {
	inv1, inv2 int
}

func topologicalSortingAndIsDag(rel map[IOCRelationKey]bool, invocations set.Interface) ([]int, bool, int) {
	l := make([]int,0)
	q := set.New()
	// add all nodes with no incoming edges
	invsWithIncoming := make(map[int]int) // from inv to number of incoming edges. Is initialized to 0?
	for k,v := range rel {
		if v == true {
			invsWithIncoming[k.inv2]++
		}
	}

	Debug(6, "invs with incoming: %v", invsWithIncoming)
	for i := range invocations.List() {
		numIncoming, existsInInvsWithIncoming := invsWithIncoming[i]
		if !existsInInvsWithIncoming || numIncoming == 0 {
			Debug(6, "Inv %v has no incoming edges, adding it", i)
			q.Add(i)
		}
	}

	for !q.IsEmpty() {
		n := q.Pop().(int)
		Debug(6, "Adding %v", n)
		l = append(l,n)
		for k,v := range rel {
			if k.inv1 == n && v == true {
				m := k.inv2
				rel[IOCRelationKey{n, m}] = false
				invsWithIncoming[m]--
				if invsWithIncoming[m] == 0 {
					Debug(6, "Adding %v as having no incoming edges", m)
					q.Add(m)
				}
			}
		}
	}

	// check if rel still has edges
	isDag := true
	violatingInv := 0
	for k,v := range rel {
		if v == true {
			ImportantDebug("There is a cycle in rel %v with remaining edge (%v,%v)", rel, k.inv1, k.inv2)
			isDag = false
			violatingInv = k.inv1 // Not sure this is the right invocation. Check full execution in debugs to be sure
			break
		}
	}

	if !isDag {
		return make([]int,0), false, violatingInv
	}

	Debug(2, "DAG: %v", l)

	return l, true, 0
}

func (checker *Checker) getRelevantInvocations() (set.Interface) {
	invocations := set.New()
	for i := range checker.invocationsRanges {
		// Only non-ignored ones:
		invIdx := i
		if !checker.transactionSegments[invIdx].mayIgnore {
			invocations.Add(invIdx)
		}
	}

	return invocations
}

func (checker *Checker) calcIOCRelation(commuteMatrix map[CommutativityMatrixKey]CommutativityMatrixValue, invocations set.Interface) (map[IOCRelationKey]bool) {
	iocRelation := make(map[IOCRelationKey]bool)
	Debug(3, "Working on commutativity matrix %v", commuteMatrix)

	for i1 := range invocations.List() {
		for i2 := range invocations.List() {
			inv1Segment1 := checker.transactionSegments[i1]
			inv2Segment1 := checker.transactionSegments[i2]

			if inv1Segment1.contract == inv2Segment1.contract {
				// Check if inv2 enclosed in inv1
				suffixInv1 := checker.getSuffix(inv1Segment1, i1)
				Debug(3, "inv1Segment1 %v, inv2Segment1 %v, suffixInv1 %v", inv1Segment1, inv2Segment1, suffixInv1)
				// If (1) inv1 starts before inv2 and (2) last segment in inv1 is after the start of inv2, then inv2 is enclosed in inv1
				if inv1Segment1.indexInTransaction < inv2Segment1.indexInTransaction &&
					len(suffixInv1) > 0 && // If suffixInv1 after inv1Segment1 is empty, then inv1 can't enclose inv2
					suffixInv1[len(suffixInv1)-1].indexInTransaction > inv2Segment1.indexInTransaction {
					// Now, get all segments of call inv2
					inv2Segments := checker.getInvocationSegments(inv2Segment1)
					// For each segment in inv2, check if i1 must be before i2 as the prefix does not commute with i1
					for segInv2Idx := range inv2Segments {
						segInv2 := inv2Segments[segInv2Idx]
						commutativity := commuteMatrix[CommutativityMatrixKey{i1, segInv2.indexInTransaction}]
						Debug(3, "i2 [ i1: commutativity %v for %v and %v", commutativity, i1, segInv2)
						if commutativity.prefixCommute == false && commutativity.suffixCommute == true {
							iocRelation[IOCRelationKey{i1, i2}] = true
						}
					}
				}

				// Now the inverse: for inv2 encloses inv1
				suffixInv2 := checker.getSuffix(inv2Segment1, i2)
				Debug(3, "inv2Segment1 %v, inv1Segment1 %v, suffixInv1 %v", inv2Segment1, inv1Segment1, suffixInv2)
				if inv2Segment1.indexInTransaction < inv1Segment1.indexInTransaction &&
					len(suffixInv2) > 0 && // If suffixInv2 after inv2Segment1 is empty, then inv2 can't enclose inv1
					suffixInv2[len(suffixInv2)-1].indexInTransaction > inv1Segment1.indexInTransaction {
						inv1Segments := checker.getInvocationSegments(inv1Segment1)
						for segInv1Idx := range inv1Segments {
							segInv1 := inv1Segments[segInv1Idx]
							commutativity := commuteMatrix[CommutativityMatrixKey{i2, segInv1.indexInTransaction}]
							Debug(3, "i1 [ i2: commutativity %v for %v and %v", commutativity, i2, segInv1)
							if commutativity.prefixCommute == true && commutativity.suffixCommute == false {
								iocRelation[IOCRelationKey{i1, i2}] = true
							}
				}
				}

			} else {
				iocRelation[IOCRelationKey{i1,i2}] = false
			}
		}
	}

	return iocRelation
}

func (checker *Checker) checkECF() {
	Debug(2, "Transaction segments: (%v) %v", len(checker.transactionSegments), checker.transactionSegments)
	if len(checker.transactionSegments) == 1 { // If there is just 1 segment in the transaction, no point in checking it! Optimization
		return
	}
	Debug(2, "Invocations: %v, and invocations ranges: %v", checker.invocations, checker.invocationsRanges)

	// Get the (non-ignored) invocations
	invocations := checker.getRelevantInvocations()
	Debug(2, "Relevant invocations: %v", invocations)
	
	// Build commutativity matrix
	commuteMatrix, isEcf, contract, depth, idxInTransaction := checker.buildCommutativityMatrix(invocations)
	if !isEcf {
		ImportantDebug("Not ECF because found non commutative segments")
		reportNonECF(contract, depth, idxInTransaction, len(checker.transactionSegments))
		return
	}
	Debug(2, "Commutativity matrix: %v", commuteMatrix)

	// Build IOC relation
	iocRelation := checker.calcIOCRelation(commuteMatrix, invocations)
	Debug(2, "iocRelation: %v", iocRelation);

	_, isDag, violatingInv := topologicalSortingAndIsDag(iocRelation, invocations)
	if !isDag {
		ImportantDebug("Transaction is not ECF, as invocation constraint order graph has a cycle")
		violatingInvFirstSegment := checker.transactionSegments[violatingInv]
		reportNonECF(violatingInvFirstSegment.contract.Hex(), violatingInvFirstSegment.depth, violatingInvFirstSegment.indexInTransaction, len(checker.transactionSegments))
	}
}

// UponEVMStart is called each time the EVM is run (due to a call or otherwise)
func (checker *Checker) UponEVMStart(evm *Interpreter, contract *Contract) {
	if DISABLE_CHECKER {
		return
	}

	Debug(5, "EVM was Run %s", "")
	checker.numOfTransactionsCheckedSoFar++
	if checker.numOfTransactionsCheckedSoFar%10000 == 0 {
		Debug(1, "Checked %d transactions so far in this run", checker.numOfTransactionsCheckedSoFar)
	}

	if checker.TransactionID == 0 {
		// Read from database
		var lastTransactionID int
		qErr := checker.dbHandler.QueryRow("select txId from LAST_TRANSACTION_ID").Scan(&lastTransactionID)
		if qErr != nil {
			ImportantDebug("Failed to get last tx id")
		} else {
			checker.TransactionID = lastTransactionID
			Debug(1, "Got transaction ID from last run: %v", checker.TransactionID)
		}
	}

	checker.TransactionID++

	// When the call is from a regular user, i.e. when the call stack is empty/quiescent state, we also record the origin, block number, and time
	if checker.evmStack.Len() == 0 {
		checker.origin = &evm.evm.Origin
		checker.blockNumber = evm.evm.BlockNumber
		checker.time = evm.evm.Time
		checker.processTime = time.Now()
	}

	// Create a new Segment
	if checker.evmStack.Len() == 0 || checker.isRealCall {
		checker.PushNewSegmentFromStart(contract)
	}

	checker.evmStack.Push(checker.evmStack.Len() == 0 || checker.isRealCall)

	// Reset isRealCall until the next CALL opcode is seen
	checker.isRealCall = false
}

// UponEVMEnd is called each time the EVM run's ends (due to a return or otherwise)
func (checker *Checker) UponEVMEnd(evm *Interpreter, contract *Contract) {
	if DISABLE_CHECKER {
		return
	}

	// We pop from running segments only if the evmStack top is true (i.e. a real call, and not a delegated one)
	activeCallIsARealCall := checker.evmStack.Pop().(bool)
	Debug(5, "Finished a real call? %v", activeCallIsARealCall)
	if checker.runningSegments.Len() > 1 && activeCallIsARealCall == true {
		checker.runningSegments.Pop()
		checker.PushNewSegmentFromEnd()
	}

	if checker.runningSegments.Len() == 1 && activeCallIsARealCall {
		FirstSegment := checker.runningSegments.Pop().(*Segment)

		Debug(2, "Transaction ended (Block #%v, contract %v). Checking if ECF", evm.evm.BlockNumber, FirstSegment.contract.Hex())

		ecfCheckStartTime := time.Now()
		checker.checkECF()
		ecfCheckDuration := time.Since(ecfCheckStartTime)
		totalProcessDuration := time.Since(checker.processTime)
		Debug(2, "ECF check (Block #%v, contract %v) took %s / %s total", evm.evm.BlockNumber, FirstSegment.contract.Hex(), ecfCheckDuration, totalProcessDuration)
	}

	if checker.evmStack.Len() == 0 {
		checker.origin = nil
		checker.blockNumber = nil
		checker.time = nil
	}
}

// UponSStore is called upon each SSTORE opcode called
func (checker *Checker) UponSStore(evm *EVM, contract *Contract, loc common.Hash, val *big.Int) {
	if DISABLE_CHECKER {
		return
	}

	checker.GetLastSegment().writeSet.Add(loc)
}

// UponSLoad is called upon each SLOAD opcode called
func (checker *Checker) UponSLoad(evm *EVM, contract *Contract, loc common.Hash, val *big.Int) {
	if DISABLE_CHECKER {
		return
	}

	// Add only if not in writeSet.
	ws := checker.GetLastSegment().writeSet
	if ws.Has(loc) {
		Debug(2, "Read location %v already appears in writeset %v", loc, ws)
	}

	checker.GetLastSegment().readSet.Add(loc)
}

// UponCall is called upon each CALL opcode called
func (checker *Checker) UponCall(evm *EVM, contract *Contract, callee common.Address, value *big.Int, input []byte) {
	if DISABLE_CHECKER {
		return
	}

	checker.isRealCall = true
}