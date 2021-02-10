using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Automata.BooleanAlgebras;
using System.Runtime.CompilerServices;

namespace Microsoft.Automata
{

    public partial class CountingAutomaton<S> : Automaton<Tuple<Maybe<S>, Sequence<CounterOperation>>>
    {
        /// <summary>
        /// Maps a counting state to its associated counter
        /// </summary>
        internal ICounter[] countingStates;
        public double[] mapStateToCycles;
        /// <summary>
        /// Maps a state to the underlying regex AST node
        /// </summary>
        SymbolicRegexNode<S>[] stateMap;
        /// <summary>
        /// Array of all counters, counter with identifier i is the element counters[i]
        /// </summary>
        internal ICounter[] counters;

        public double MaxSumCounter()
        {
            double max = 0;
            if (counters.Length == 0)
                return -1;
            for (int i = 0; i < counters.Length; i++)
            {
                max += counters[i].UpperBound;
            }
            return max;
        }

        public double MaxCounter()
        {
            double max = 0;
            if (counters.Length == 0)
                return -1;
            for (int i = 0; i < counters.Length; i++)
            {
                if(max < counters[i].UpperBound)
                    max = counters[i].UpperBound;
            }
            return max;
        }

        internal ICharAlgebra<S> solver;

        private Dictionary<CounterOp, CsUpdate> mapOp = new Dictionary<CounterOp, CsUpdate> {
                            { CounterOp.EXIT, CsUpdate.EXIT},
                            { CounterOp.EXIT_SET1, CsUpdate.ADD1_EXIT},
                            { CounterOp.INCR, CsUpdate.INCR},
                            { CounterOp.SET0, CsUpdate.ADD0},
                            { CounterOp.SET1, CsUpdate.ADD1}
                        };

        internal CountingAutomaton(Automaton<Tuple<Maybe<S>, Sequence<CounterOperation>>> aut,
            SymbolicRegexNode<S>[] stateMap, ICounter[] countingStates, List<ICounter> counters) : base(aut)
        {
            this.countingStates = countingStates;
            this.stateMap = stateMap;
            this.solver = ((CABA<S>)Algebra).builder.solver;
            this.cntCount = aut.cntCount;
            this.cntStates = stateMap.Length;
            if (countingStates != null)
            {
                this.counters = new ICounter[aut.cntCount];
                foreach (var counter in counters)
                {
                    this.counters[counter.CounterId] = counter;
                }
            }
            else
                this.counters = new ICounter[0];
        }

        
        /// <summary>
        /// Returns the final state condition of a final state. 
        /// </summary>
        public Sequence<CounterOperation> GetFinalStateCondition(int state)
        {
            if (!IsFinalState(state))
                throw new AutomataException(AutomataExceptionKind.ArgumentMustBeFinalState);

            if (countingStates[state] != null && countingStates[state].LowerBound > 0)
            {
                return new Sequence<CounterOperation>(new CounterOperation(countingStates[state], CounterOp.EXIT));
            }
            else
                return Sequence<CounterOperation>.Empty;
        }

        public override string DescribeState(int state)
        {
            string s;
            if (__hideDerivativesInViewer)
                s = SpecialCharacters.q(state);
            else
                s = stateMap[state].ToString();
            if (countingStates != null)
            {
                if (IsFinalState(state) && IsCountingState(state))
                {
                    s += "\n(";
                    var f = GetFinalStateCondition(state);
                    for (int i = 0; i < f.Length; i++)
                    {
                        if (i > 0)
                            s += SpecialCharacters.AND;
                        var op = f[i];
                        s += op.ToString();
                    }
                    s += ")" + SpecialCharacters.CHECKMARK;
                }
                else if (IsCountingState(state))
                    s += "\n(" + SpecialCharacters.c(countingStates[state].CounterId) + ")";
            }
            return s;
        }

        public override string DescribeStartLabel()
        {
            
            if (IsCountingState(InitialState))
            {
                var c = countingStates[InitialState];
                return string.Format("{0}{1}0", SpecialCharacters.c(c.CounterId), SpecialCharacters.ASSIGN);
            }
            else
                return "";
        }

        public override string DescribeLabel(Tuple<Maybe<S>, Sequence<CounterOperation>> lab)
        {
            string s = "";
            if (lab.Item1 != Maybe<S>.Nothing)
            {
                s += lab.Item1.Element.ToString();
                s += SpecialCharacters.MIDDOT;
            }
            if (lab.Item2.Length > 1)
                s += lab.Item2.ToString();
            else if (lab.Item2.Length == 1)
                s += lab.Item2[0].ToString();
            return s;
        }

        /// <summary>
        /// Returns true if q is a counting-state (q is associated with a counter)
        /// </summary>
        /// <param name="q">given state</param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool IsCountingState(int q)
        {
            if (countingStates == null)
                return false;
            else
                return countingStates[q] != null;
        }

        Dictionary<int, bool> IsSingletonCountingState_result = new Dictionary<int, bool>();
        /// <summary>
        /// Returns true if q is a counting-state that only needs one copy of the counter.
        /// A sufficient condition is when no incoming transition overlaps with any loop.
        /// </summary>
        /// <param name="q">given state</param>
        public bool IsSingletonCountingState(int q)
        {
            bool res;
            if (!IsSingletonCountingState_result.TryGetValue(q, out res))
            {
                S loopCond = solver.False;
                foreach (var loop in GetMovesFrom(q))
                {
                    if (loop.IsSelfLoop && loop.Label.Item1.IsSomething)
                    {
                        loopCond = solver.MkOr(loopCond, loop.Label.Item1.Element);
                    }
                }
                res = true;
                foreach (var trans in GetMovesTo(q))
                {
                    if (!trans.IsSelfLoop)
                    {
                        if (solver.IsSatisfiable(solver.MkAnd(trans.Label.Item1.Element, loopCond)))
                        {
                            res = false;
                            break;
                        }
                    }
                }
                IsSingletonCountingState_result[q] = res;
                return res;
            }
            return res;
        }

        public bool Satisfy(Tuple<Maybe<S>, Sequence<CounterOperation>> label, CsConditionSeq conditions)
        {
            if (label.Item2.IsEmpty)
                return true;
            for (int i = 0; i < label.Item2.Count(); i++)
            {
                switch(label.Item2[i].OperationKind)
                {
                    case CounterOp.SET0:
                        break;
                    case CounterOp.INCR:
                        if (conditions[label.Item2[i].Counter.CounterId] == CsCondition.HIGH)
                            return false;
                        break;
                    case CounterOp.EXIT:
                        if (conditions[label.Item2[i].Counter.CounterId] == CsCondition.LOW)
                            return false;
                        break;
                    case CounterOp.EXIT_SET1:
                        if (conditions[label.Item2[i].Counter.CounterId] == CsCondition.LOW)
                            return false;
                        break;
                }
            }
            return true;
        }


        /// <summary>
        /// Returns the counter associated with the state q.
        /// The state q must be a couting state.
        /// </summary>
        /// <param name="q">given counting state</param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public ICounter GetCounter(int q)
        {
            return countingStates[q];
        }

        /// <summary>
        /// Returns the counter with the given id
        /// </summary>
        /// <param name="q">given counter id</param>
        public ICounter GetCounterWithId(int counterId)
        {
            return counters[counterId];
        }

        /// <summary>
        /// Returns true if q is a counting state and outputs the counter of q.
        /// Returns false otherwise and sets counter to null.
        /// </summary>
        public bool TryGetCounter(int q, out ICounter counter)
        {
            try
            {
                counter = countingStates[q];
                return true;
            }
            catch
            {
                counter = null;
                return false;
            }            
        }

        private int GetHashCode(int a, CsUpdateSeq b)
        {
            return (b.GetHashCode() * 10000) + a;
        }

        private Tuple<CsUpdateSeq, int, bool, HashSet<int>, HashSet<int>, bool> GetTargetInfo(Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>[] moves, S minterm, CsConditionSeq rule, PowerSetStateBuilder dfaStateBuilder)
        {
            // initialize update for each counter
            var updates = new CsUpdate[this.cntCount];
            HashSet<int> targetStates = new HashSet<int>();
            bool final = false; // target state is final
            bool nonCond = false;    // there is non-conditional final state
            HashSet<int> finalCounters = new HashSet<int>();
            HashSet<int> updatedCounters = new HashSet<int>();
      
            var mapOp = new Dictionary<CounterOp, CsUpdate> {
                { CounterOp.EXIT, CsUpdate.EXIT},
                { CounterOp.EXIT_SET1, CsUpdate.ADD1_EXIT},
                { CounterOp.INCR, CsUpdate.INCR},
                { CounterOp.SET0, CsUpdate.ADD0},
                { CounterOp.SET1, CsUpdate.ADD1}
            };
            for (int i = 0; i < this.cntCount; i++)
            {
                updates[i] = CsUpdate.NOOP;
            }
            for (int i = 0; i < moves.Length; i++)
            {
                var move = moves[i];
                if (move.Label.Item1.Element.Equals(minterm))
                {
                    // filter moves according to the counter conditions
                    if (this.Satisfy(move.Label, rule))
                    {
                        targetStates.Add(move.TargetState);
                        int sourceCounter = -1;
                        int targetCounter = -1;
                        if (this.IsCountingState(move.TargetState))
                        {
                            targetCounter = this.GetCounter(move.TargetState).CounterId;
                        }
                        if (this.IsCountingState(move.SourceState))
                        {
                            sourceCounter = this.GetCounter(move.SourceState).CounterId;
                        }
                        if (this.IsFinalState(move.TargetState))
                        {
                            final = true;
                            // there is no non-conditional final state
                            if (targetCounter != -1)
                                finalCounters.Add(targetCounter);
                            else
                                nonCond = true; // noncond final state                              
                        }
                        // NOOP on the edge
                        if (move.Label.Item2.IsEmpty)
                        {
                            // target and source states are counting states
                            if (targetCounter != -1)
                            {
                                if (sourceCounter != -1)
                                {
                                    updates[sourceCounter] |= CsUpdate.COPY;
                                    updatedCounters.Add(sourceCounter);
                                }
                                else
                                {
                                    updates[targetCounter] |= CsUpdate.EXIT;
                                    updatedCounters.Add(targetCounter);
                                }
                            }
                            else if (sourceCounter != -1)
                            {
                                updates[sourceCounter] |= CsUpdate.EXIT;
                                updatedCounters.Add(sourceCounter);
                            }
                        }
                        else
                        {
                            // iterate through updates on the move
                            for (int j = 0; j < move.Label.Item2.Count(); j++)
                            {
                                var id = move.Label.Item2[j].Counter.CounterId;
                                updates[id] |= mapOp[moves[i].Label.Item2[j].OperationKind];
                                updatedCounters.Add(id);
                            }
                        }
                    }
                }
                      
            }
            
            return new Tuple<CsUpdateSeq, int, bool, HashSet<int>, HashSet<int>, bool>(CsUpdateSeq.Mk(updates), dfaStateBuilder.MakePowerSetState(targetStates), final, updatedCounters, finalCounters, nonCond);
        }

        //private List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> EnabledTrans(List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> moves, CsConditionSeq rule, S symbol, out HashSet<int> targetStates, out CsUpdateSeq updateSeq)
    /*    private void EnabledTrans(List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> moves, CsConditionSeq rule, out CsUpdate[] updates, S symbol, out HashSet<int> targetStates, out CsUpdateSeq updateSeq)
        {
            var cnt = this.counters.Count();
            // filter transitions that goes from a final state to another final state
            // and transitions that satisfy the minterm rule
            targetStates = new HashSet<int>();
            //var list = new List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>>();
            updates = new CsUpdate[cnt];
            for (int i = 0; i < cnt; i++)
            {
                updates[i] = CsUpdate.NOOP;
            }
            var mapOp = new Dictionary<CounterOp, CsUpdate> {
                { CounterOp.EXIT, CsUpdate.EXIT},
                { CounterOp.EXIT_SET1, CsUpdate.ADD1_EXIT},
                { CounterOp.INCR, CsUpdate.INCR},
                { CounterOp.SET0, CsUpdate.ADD0},
                { CounterOp.SET1, CsUpdate.ADD1}
            };
            for (int i = 0; i < moves.Count(); i++)
            {
                if (moves[i].Label.Item1.Element.Equals(symbol) && this.Satisfy(moves[i].Label, rule))
                {
                    //list.Add(moves[i]);
                    targetStates.Add(moves[i].TargetState);
                    if (moves[i].Label.Item2.IsEmpty)
                    {
                        if (this.IsCountingState(moves[i].TargetState) && this.IsCountingState(moves[i].SourceState))
                        {
                            // noop on the bigger loop - copy set
                            var counter = this.GetCounter(moves[i].TargetState).CounterId;
                            updates[counter] |= CsUpdate.COPY;
                            if ((updates[counter] & CsUpdate.COPY_INCR) == CsUpdate.COPY_INCR)
                            {
                                throw new AutomataException(AutomataExceptionKind.InternalError_Conflict);
                            }
                        }
                    }
                    for (int j = 0; j < moves[i].Label.Item2.Count(); j++)
                    {
                        var id = moves[i].Label.Item2[j].Counter.CounterId;
                        updates[id] |= mapOp[moves[i].Label.Item2[j].OperationKind];
                        if ((updates[id] & CsUpdate.COPY_INCR) == CsUpdate.COPY_INCR)
                        {
                            throw new AutomataException(AutomataExceptionKind.InternalError_Conflict);
                        }
                    }
                }
            }

            updateSeq = CsUpdateSeq.Mk(updates);
            var cd = updateSeq.ToString();
        }
*/

        /// <summary>
        /// Optimized version of the compile function (merging transitions with same update).
        /// </summary>
        /// <param name="mode">0 - generate HIGH, MIDDLE, LOW always, 1 - generate MIDDLE or LOW only if needed</param>
        /// <returns></returns>
        public CsAutomatonOpt<S> CompileOpt(int _mode = 0, bool graphs = false)
        {
            // pass to next function
            IBooleanAlgebra<Tuple<Maybe<S>, Sequence<CounterOperation>>> solver = this.Algebra;
            var CABAsolver = ((CABA<S>)Algebra).builder.solver;
            CsAlgebra<S> productAlgebra = new CsAlgebra<S>(CABAsolver, this.counters);
            var stack = new Stack<int>();
            var setOfStates = new List<int>();
            Dictionary<int, int> mapStates = new Dictionary<int, int>();    // map index of state of states to state of DCA
            var usedCounters = new Dictionary<int, HashSet<int>>();
            var updatedCounters = new Dictionary<int, HashSet<int>[]>();
            var finalCounters = new Dictionary<int, HashSet<int>>();
            List<int> finalStateDCA = new List<int>();
            var moves = new List<Move<CsLabel<S>>>();
            var states = this.States.ToArray();
            var transTable = new Dictionary<int, List<Tuple<CsConditionSeq, Tuple<CsUpdate[], int>>>[]>();
            //the sink state is represented implicitly, there is no need to make B total
            PowerSetStateBuilder dfaStateBuilder = PowerSetStateBuilder.Create(states);
            var partitions = CABAsolver.GetPartition();
            var minSymbols = new S[partitions.Count()];
            var minterms = new int[partitions.Length];
            Dictionary<int, int[]> mapConf = new Dictionary<int, int[]>();
            for(int i = 0; i < partitions.Length; i++)
            {
                minterms[i] = CABAsolver.MintermIndex(partitions[i]);
                minSymbols[i] = partitions[i];
            }
            int limit = 256;
            int[] precomputed = new int[limit+1];            
            for (int j = 0; j <= limit; j++)
            {
                precomputed[j] = CABAsolver.MintermIndex(CABAsolver.MkCharConstraint((char)j));
            }
            // initial state
            var startID = dfaStateBuilder.MakePowerSetState(new List<int> { this.InitialState });
            stack.Push(startID);        // current state ID
            setOfStates.Add(startID);   // remember all already handled states
            mapStates[startID] = 1;     // map state id to state of DCA
            int countStates = 1;

            if (IsCountingState(this.InitialState))
            {
                var counter = this.GetCounter(this.InitialState);
                mapConf[startID] = new int[this.cntStates];
                mapConf[startID][counter.CounterId] = 1;
                // check if the initial state is final
                if (this.IsFinalState(this.InitialState))
                {
                    finalStateDCA.Add(1);   // add initial state to final state DCA 
                    finalCounters[1] = new HashSet<int> {counter.CounterId};
                }
            }               
            else
            {
                mapConf[startID] = new int[this.cntStates];
                // check if the initial state is final
                if (this.IsFinalState(this.InitialState))
                {
                    finalStateDCA.Add(1);   // add initial state to final state DCA 
                    finalCounters[1] = new HashSet<int>();
                }
            }
            CsConditionSeq trueSeq = null;
            if (this.cntCount != 0 || graphs)
                trueSeq = CsConditionSeq.MkTrue(this.cntCount);

            int countMoves = 0;
            while (stack.Count > 0)
            {
                var sourceID = stack.Pop();
                int sourceState = mapStates[sourceID];
                var NCAStates = dfaStateBuilder.GetMembers(sourceID).ToArray();
                // counting states of the powerset
                var countingStates = new HashSet<int>();
                usedCounters[sourceState] = new HashSet<int>();
                transTable[sourceState] = new List<Tuple<CsConditionSeq, Tuple<CsUpdate[], int>>>[minterms.Length];
                updatedCounters[sourceState] = new HashSet<int>[minterms.Count()];
                // go through the powerset
                var cs = 0;
                for (var i = 0; i < NCAStates.Length; i++)
                {
                    var state = NCAStates[i];
                    if (this.IsCountingState(state))
                    {
                        countingStates.Add(state);
                        cs++;
                        usedCounters[sourceState].Add(GetCounter(state).CounterId);
                    }
                }
                var movesOut = this.GetMovesFromStates(NCAStates).ToArray();
                var symbolMinterms = new List<S>();
                CsConditionSeq[] counterMinterms = new CsConditionSeq[]{ trueSeq };
                if(cs != 0 || graphs)
                {
                    counterMinterms = this.GenerateMinterms(ConsList<int>.Create(countingStates), usedCounters[sourceState].ToList(), movesOut, _mode, trueSeq).ToArray();
                }
                var tranGroups = new Dictionary<int, Tuple<CsUpdateSeq, CsConditionSeq, CsPred<S>, int>>();
                foreach (var move1 in movesOut)
                {
                    var minterm = move1.Label.Item1.Element;
                    if (symbolMinterms.Contains(minterm) || (ulong)((object)minterm) == 0)    //  skip final transitions
                        continue;
                    else
                        symbolMinterms.Add(minterm);

                    var symbol = CABAsolver.MintermIndex(minterm);
                    updatedCounters[sourceState][symbol] = new HashSet<int>();
                    transTable[sourceState][symbol] = new List<Tuple<CsConditionSeq, Tuple<CsUpdate[], int>>>();
                    for (var r = 0; r < counterMinterms.Length; r++)
                    {
                        var rule = counterMinterms[r];
                        // initialize update for each counter
                        CsUpdate[] updates = null;
                        if (this.cntCount != 0 || graphs)
                        {
                            updates = new CsUpdate[this.cntCount]; 
                            for (int i = 0; i < this.cntCount; i++)
                                updates[i] = CsUpdate.NOOP;
                        }
                        // set of target states
                        HashSet<int> targetStates = new HashSet<int>();
                        var fc = new HashSet<int>();
                        bool final = false; // target state is final
                        bool nonCond = false;    // there is non-conditional final state                       
                                              
                        for (int i = 0; i < movesOut.Length; i++)
                        {
                            var move = movesOut[i];
                            if (move.Label.Item1.Element.Equals(minterm))
                            {
                                // filter moves according to the counter conditions
                                if (this.Satisfy(move.Label, rule))
                                {
                                    targetStates.Add(move.TargetState);
                                    int sourceCounter = -1;
                                    int targetCounter = -1;
                                    if (this.IsCountingState(move.TargetState))
                                    {
                                        targetCounter = this.GetCounter(move.TargetState).CounterId;
                                    }
                                    if (this.IsCountingState(move.SourceState))
                                    {
                                        sourceCounter = this.GetCounter(move.SourceState).CounterId;
                                    }
                                    if (this.IsFinalState(move.TargetState))
                                    {
                                        final = true;
                                        // there is no non-conditional final state
                                        if (targetCounter != -1)
                                            fc.Add(targetCounter);
                                        else
                                            nonCond = true; // noncond final state                              
                                    }
                                    // NOOP on the edge
                                    if (move.Label.Item2.IsEmpty)
                                    {
                                        // target and source states are counting states
                                        if (targetCounter != -1)
                                        {
                                            if (sourceCounter != -1)
                                            {
                                                updates[sourceCounter] |= CsUpdate.COPY;
                                                updatedCounters[sourceState][symbol].Add(sourceCounter);
                                                if (updates[sourceCounter] > CsUpdate.COPY)
                                                    throw new AutomataException(AutomataExceptionKind.InternalError_Conflict);
                                            }
                                            else
                                            {
                                                updates[targetCounter] |= CsUpdate.EXIT;
                                                updatedCounters[sourceState][symbol].Add(targetCounter);
                                            }
                                        }
                                        else if (sourceCounter != -1)
                                        {
                                            updates[sourceCounter] |= CsUpdate.EXIT;
                                            updatedCounters[sourceState][symbol].Add(sourceCounter);
                                        }
                                    }
                                    else
                                    {
                                        // iterate through updates on the move
                                        for (int j = 0; j < move.Label.Item2.Count(); j++)
                                        {
                                            var id = move.Label.Item2[j].Counter.CounterId;
                                            updates[id] |= mapOp[move.Label.Item2[j].OperationKind];
                                            updatedCounters[sourceState][symbol].Add(id);
                                          //  if (updates[id] > CsUpdate.COPY)
                                            //    throw new Exception("ERROR: nonmonadic regex!");
                                        }
                                    }
                                }
                            }
                        }
                        var target = dfaStateBuilder.MakePowerSetState(targetStates);

                        // no target state
                        if (target == 0)
                            continue;
                        // if automata does not have the target state, add the target state
                        var tgt = -1;
                        
                        if (!setOfStates.Contains(target))
                        {
                            // push the target state to stack
                            setOfStates.Add(target);
                            // map target state ID to state of DCA
                            countStates++;
                            mapStates[target] = countStates;
                            tgt = mapStates[target];
                            // store target state ID to stack                          
                            stack.Push(target);
                            // target state is a final state
                            if (final)
                            {
                                finalStateDCA.Add(tgt);
                                // there is some final counter
                                if (!nonCond)
                                {
                                    // conditional final state, remember final counters
                                    finalCounters[tgt] = fc;
                                }                                   
                                else
                                {
                                    // non-conditional final state
                                    finalCounters[tgt] = new HashSet<int>();
                                }                                   
                            }
                            var tStates = targetStates.ToArray();
                            mapConf[tgt] = new int[this.cntStates];
                            for (int i = 0; i < tStates.Length; i++)
                            {
                                if (IsCountingState(tStates[i]))
                                {
                                    mapConf[tgt][this.GetCounter(tStates[i]).CounterId] += 1;
                                }
                            }                                
                        }
                        else
                        {
                            tgt = mapStates[target];
                            // target state is final and there is some final counter
                            if (final && !nonCond)
                                finalCounters[tgt].UnionWith(fc);                            
                        }
                        if (graphs)
                        {
                            var newUpdates = CsUpdateSeq.Mk(updates);
                            var pred = productAlgebra.MkPredicate(minterm, rule);
                            if (!tranGroups.Keys.Contains(this.GetHashCode(tgt, newUpdates)))
                                tranGroups[this.GetHashCode(tgt, newUpdates)] = Tuple.Create(newUpdates, rule, pred, tgt);
                            else
                                tranGroups[this.GetHashCode(tgt, newUpdates)] = Tuple.Create(newUpdates, tranGroups[this.GetHashCode(tgt, newUpdates)].Item2 | rule, tranGroups[this.GetHashCode(tgt, newUpdates)].Item3 | pred, tgt);
                        }
                        countMoves++;
                        transTable[sourceState][symbol].Add(new Tuple<CsConditionSeq, Tuple<CsUpdate[], int>>(rule, new Tuple<CsUpdate[], int>(updates, tgt)));
                    }  
                }
                foreach (var move in tranGroups.Values)
                    moves.Add(Move<CsLabel<S>>.Create(sourceState, move.Item4, CsLabel<S>.MkTransitionLabel(move.Item3, move.Item2, productAlgebra, move.Item1, ((CABA<S>)this.Algebra).builder.solver.PrettyPrint)));
            }
            var autDet = Automaton<CsLabel<S>>.Create(null, 1, finalStateDCA, moves);
          
            CsAutomatonOpt<S> autOpt = new CsAutomatonOpt<S>(CABAsolver, autDet, countMoves, dfaStateBuilder, transTable, countStates, finalStateDCA.ToArray(), counters, this.cntCount, precomputed, minterms, mapStates, finalCounters, updatedCounters, usedCounters, minSymbols, mapConf);
            return autOpt;
        }       

        public override IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMoves()
        {
            //provide consolidated view of moves
            var guardMap = new Dictionary<Tuple<int, int, Sequence<CounterOperation>>, S>();
            foreach (var move in base.GetMoves())
            {
                if (move.Label.Item1.IsSomething)
                {
                    var key = new Tuple<int, int, Sequence<CounterOperation>>(move.SourceState, move.TargetState, move.Label.Item2);
                    S guard;
                    if (guardMap.TryGetValue(key, out guard))
                        guardMap[key] = ((CABA<S>)(base.Algebra)).builder.solver.MkOr(move.Label.Item1.Element, guard);
                    else
                        guardMap[key] = move.Label.Item1.Element;
                }
            }
            foreach (var entry in guardMap)
                yield return Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>.Create(
                    entry.Key.Item1, entry.Key.Item2,
                    new Tuple<Maybe<S>, Sequence<CounterOperation>>(Maybe<S>.Something(entry.Value), entry.Key.Item3)
                    );
        }

        /// <summary>
        /// Creates counter minterms for the given set of counting states and input 
        ///  icate.
        /// </summary>
        /// <param name="list">list of counting states, possibly empty i.e. null</param>
        /// <param name="a">input predicate</param>
        /// <returns></returns>
      /*  private IEnumerable<CsConditionSeq> GenerateCounterMinterms(ConsList<int> list, S a, int _mode = 0)
        {
            if (list == null)
                yield return CsConditionSeq.MkTrue(this.counters.Count());
            else
            {
                var a_moves = new List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>>(GetMovesFrom(list.First, a)).ToArray();
                var ma = a_moves.ToList();
                var incr_exists = Array.Exists(a_moves, m => !m.Label.Item2.IsEmpty && m.Label.Item2.First.OperationKind == CounterOp.INCR);
                var exit_exists = Array.Exists(a_moves, m => !m.Label.Item2.IsEmpty && m.Label.Item2.First.OperationKind != CounterOp.INCR);
                var i = GetCounter(list.First).CounterId;
                foreach (var seq in GenerateCounterMinterms(list.Rest, a, _mode))
                {
                    if (a_moves.Length > 0)
                    {   // this can be just in the case that there is one exit or one incr for all counting states not just first in a list
                        if (incr_exists || exit_exists)
                        {
                            if (_mode == 1)
                            {
                                if (this.counters[i].LowerBound != 0)
                                {
                                    yield return seq.Update(i, CsCondition.LOW);
                                }
                                if (!(IsSingletonCountingState(list.First) && GetCounter(list.First).LowerBound == GetCounter(list.First).UpperBound))
                                {
                                    yield return seq.Update(i, CsCondition.MIDDLE);
                                }
                                yield return seq.Update(i, CsCondition.HIGH);
                            }
                            else
                            {
                                yield return seq.Update(i, CsCondition.LOW);
                                // if mode set, skip is lowerbound is equal upper bound
                                yield return seq.Update(i, CsCondition.MIDDLE);
                                yield return seq.Update(i, CsCondition.HIGH);
                            }
                        }
                        else
                        { // new code
                            yield return seq;//throw new AutomataException(AutomataExceptionKind.InternalError_GenerateCounterMinterms);
                        }
                    }
                    else
                        yield return seq;
                }
            }
        }*/

        /// <summary>
        /// Creates counter minterms for the given set of counting states and input predicate.
        /// </summary>
        /// <param name="list">list of counting states, possibly empty i.e. null</param>
        /// <param name="a">input predicate</param>
        /// <returns></returns>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private IEnumerable<CsConditionSeq> GenerateMinterms(ConsList<int> list,  List<int> ac, Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>[] moves, int _mode, CsConditionSeq trueSeq)
        {
            if (list == null)
                yield return trueSeq;
            else
            {
                bool exit_exists = false;
                bool incr_exists = false;
                for (int m = 0; m < moves.Length; m++)
                {
                    var move = moves[m];
                    if (move.SourceState == list.First)    // skip move that are not from a source state
                    {
                        if (!move.Label.Item2.IsEmpty)
                        {
                            if (move.Label.Item2.First.OperationKind == CounterOp.EXIT)
                                exit_exists = true;
                            else 
                                incr_exists = true;
                            if (exit_exists && incr_exists)
                                break;
                        }                        
                    }                    
                }
                var i = GetCounter(list.First).CounterId;
                foreach (var seq in GenerateMinterms(list.Rest, ac, moves, _mode, trueSeq))
                {
                    // this can be just in the case that there is one exit or one incr for all counting states not just first in a list
                     if (incr_exists || exit_exists)
                     {
                         if (_mode == 1)
                         {
                             if (this.counters[i].LowerBound != 0)
                             {
                                 yield return seq.Update(i, CsCondition.LOW);
                             }
                             if (!(IsSingletonCountingState(list.First) && GetCounter(list.First).LowerBound == GetCounter(list.First).UpperBound))
                             {
                                 yield return seq.Update(i, CsCondition.MIDDLE);
                             }
                             yield return seq.Update(i, CsCondition.HIGH);
                         }
                         else
                         {
                             yield return seq.Update(i, CsCondition.LOW);
                             yield return seq.Update(i, CsCondition.MIDDLE);
                             yield return seq.Update(i, CsCondition.HIGH);
                         }
                     }
                     else
                     {
                        if(ac.Contains(i))
                        {
                            yield return seq.Update(i, CsCondition.LOW);
                            yield return seq.Update(i, CsCondition.MIDDLE);
                            yield return seq.Update(i, CsCondition.HIGH);
                        }                        
                        yield return seq;//throw new AutomataException(AutomataExceptionKind.InternalError_GenerateCounterMinterms);
                     }
                }
            }
        }


        /* private IEnumerable<CsCondition> GenerateCounterMinterms(ConsList<int> list, S a, int _mode = 0)
         {
             if (list == null)
                 yield return CsCondition.TRUE;
             else
             {
                 var a_moves = new List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>>(GetMovesFrom(list.First, a)).ToArray();
                 var ma = a_moves.ToList();
                 var incr_exists = Array.Exists(a_moves, m => !m.Label.Item2.IsEmpty && m.Label.Item2.First.OperationKind == CounterOp.INCR);
                 var exit_exists = Array.Exists(a_moves, m => !m.Label.Item2.IsEmpty && m.Label.Item2.First.OperationKind != CounterOp.INCR);
                 var i = GetCounter(list.First).CounterId;
                 foreach (var seq in GenerateCounterMinterms(list.Rest, a, _mode))
                 {
                     if (a_moves.Length > 0)
                     {   // this can be just in the case that there is one exit or one incr for all counting states not just first in a list
                         if (incr_exists || exit_exists)
                         {
                             if (_mode == 1)
                             {
                                 if (this.counters[i].LowerBound != 0)
                                 {
                                     yield return CsCondition.LOW;
                                 }
                                 if (!(IsSingletonCountingState(list.First) && GetCounter(list.First).LowerBound == GetCounter(list.First).UpperBound))
                                 {
                                     yield return CsCondition.MIDDLE;
                                 }
                                 yield return CsCondition.HIGH;
                             }
                             else
                             {
                                 yield return CsCondition.LOW;
                                 // if mode set, skip is lowerbound is equal upper bound
                                 yield return CsCondition.MIDDLE;
                                 yield return CsCondition.HIGH;
                             }
                         }
                         else
                         { // new code
                             yield return CsCondition.TRUE;//throw new AutomataException(AutomataExceptionKind.InternalError_GenerateCounterMinterms);
                         }
                     }
                     else
                         yield return CsCondition.TRUE;
                 }
             }
         }*/


        public override IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMovesFrom(int sourceState)
        {
            foreach (var move in base.GetMovesFrom(sourceState))
                if (move.Label.Item1.IsSomething)
                    yield return move;
        }

        

        public IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMovesFromOnSymbol(int sourceState, S symbol)
        {
            foreach (var move in base.GetMovesFrom(sourceState))
                if (move.Label.Item1.IsSomething)
                    yield return move;
        }


        public IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> FilterMoves(IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> moves, int sourceState)
        {
            foreach (var move in moves)
                if (move.SourceState == sourceState)
                    yield return move;
        }

        public IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMovesFrom(int sourceState, S predicate)
        {
            var moves = base.delta[sourceState];
            for (int i = 0; i < moves.Count; i++)
            {
                var move = moves[i];
                if (move.Label.Item1.IsSomething)
                {
                    if (solver.IsSatisfiable(solver.MkAnd(predicate, move.Label.Item1.Element)))
                        yield return move;
                }
            }
        }

        public bool HasMovesTo(int targetState, S predicate)
        {
            var moves = base.deltaInv[targetState];
            for (int i = 0; i < moves.Count; i++)
            {
                var move = moves[i];
                if (move.Label.Item1.IsSomething)
                {
                    if (solver.IsSatisfiable(solver.MkAnd(predicate, move.Label.Item1.Element)))
                        return true;
                }
            }
            return false;
        }

        public IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMovesFrom(IEnumerable<int> sourceStates, S minterm)
        {
            foreach (var sourceState in sourceStates)
                foreach (var move in base.GetMovesFrom(sourceState))
                    if (move.Label.Item1.IsSomething)
                    {
                        if (solver.IsSatisfiable(solver.MkAnd(minterm, move.Label.Item1.Element)))
                            yield return move;
                    }
        }


        bool __hideDerivativesInViewer = false;
        public void ShowGraph(string name = "CountingAutomaton", bool hideDerivatives = false)
        {
            __hideDerivativesInViewer = hideDerivatives;
            base.ShowGraph(name);
        }

        public void SaveGraph(string name = "CountingAutomaton", bool hideDerivatives = false)
        {
            __hideDerivativesInViewer = hideDerivatives;
            base.SaveGraph(name);
        }

        /// <summary>
        /// Returns true if the input string is accepted by this counting automaton
        /// </summary>
        /// <param name="input">given input string</param>
        public bool IsMatch(string input)
        {
            var charsolver = ((CABA<S>)Algebra).builder.solver;
            var cs = input.ToCharArray();
            S[] inputPreds = Array.ConvertAll(cs, c => charsolver.MkCharConstraint(c));

            //current state is a pair (Q, C)
            // Q = set of normal (noncounting) states
            // C = a dictionary of counting states to counting sets  

            var Q = new HashSet<int>();
            var C = new HashSet<int>();
            var counters = new BasicCountingSet[NrOfCounters];
            //create the counting sets
            for(int j = 0; j < countingStates.Count(); j++)
                counters[countingStates[j].CounterId] = new BasicCountingSet(this.counters[j]);

            //intialize the start state of the matcher
            if (IsCountingState(InitialState))
            {
                C.Add(InitialState);
                counters[countingStates[InitialState].CounterId].Set0();
            }
            else
                Q.Add(InitialState);

            //iterate over all elements in the input list
            //if at any point both Q and C are empty then the input is rejected
            int i = 0;
            while (i < inputPreds.Length && (C.Count > 0 || Q.Count > 0))
            {
                var a = inputPreds[i];
                i += 1;

                //construct the set of target states from Q
                var Q1 = new HashSet<int>();
                var C1 = new Dictionary<int, CounterOp>();

                foreach (var q in C)
                {
                    #region moves from counting-states q
                    var c = counters[countingStates[q].CounterId];
                    foreach (var move in GetMovesFrom(q, a))
                    {
                        if (IsCountingState(move.TargetState))
                        {
                            if (move.Label.Item2[0].OperationKind == CounterOp.INCR)
                            {
                                if (move.Label.Item2.Length > 1)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);

                                CounterOp op;
                                if (C1.TryGetValue(move.TargetState, out op))
                                    C1[move.TargetState] = op | CounterOp.INCR;
                                else
                                    C1[move.TargetState] = CounterOp.INCR;
                            }
                            else if (move.Label.Item2[0].OperationKind == CounterOp.EXIT)
                            {
                                if (move.Label.Item2.Length != 2)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);
                                if (c.Max() >= countingStates[q].LowerBound)
                                {
                                    if (move.Label.Item2[1].OperationKind == CounterOp.SET0)
                                    {
                                        CounterOp op;
                                        if (C1.TryGetValue(move.TargetState, out op))
                                            C1[move.TargetState] = op | CounterOp.SET0;
                                        else
                                            C1[move.TargetState] = CounterOp.SET0;
                                    }
                                    else
                                    {
                                        if (move.Label.Item2[1].OperationKind != CounterOp.SET1)
                                            throw new AutomataException(AutomataExceptionKind.InternalError);
                                        CounterOp op;
                                        if (C1.TryGetValue(move.TargetState, out op))
                                            C1[move.TargetState] = op | CounterOp.SET1;
                                        else
                                            C1[move.TargetState] = CounterOp.SET1;
                                    }
                                }
                            }
                            else if (move.Label.Item2[0].OperationKind == CounterOp.EXIT_SET0)
                            {
                                if (move.Label.Item2.Length != 1)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);

                                if (c.Max()>= countingStates[q].LowerBound)
                                {
                                    CounterOp op;
                                    if (C1.TryGetValue(move.TargetState, out op))
                                        C1[move.TargetState] = op | CounterOp.SET0;
                                    else
                                        C1[move.TargetState] = CounterOp.SET0;
                                }
                            }
                            else if (move.Label.Item2[0].OperationKind == CounterOp.EXIT_SET1)
                            {
                                if (move.Label.Item2.Length != 1)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);

                                if (c.Max()>= countingStates[q].LowerBound)
                                {
                                    CounterOp op;
                                    if (C1.TryGetValue(move.TargetState, out op))
                                        C1[move.TargetState] = op | CounterOp.SET1;
                                    else
                                        C1[move.TargetState] = CounterOp.SET1;
                                }
                            }
                            else
                            {
                                throw new AutomataException(AutomataExceptionKind.InternalError);
                            }
                        }

                        else
                        {
                            //if exiting the counting state q is possible then 
                            //add the target state as a reachable state
                            if (c.Max()>= countingStates[q].LowerBound)
                                Q1.Add(move.TargetState);
                        }
                    }
                    #endregion
                }

                foreach (var q in Q)
                {
                    #region moves from non-counting-states q
                    foreach (var move in GetMovesFrom(q, a))
                    {
                        if (IsCountingState(move.TargetState))
                        {
                            if (move.Label.Item2.Length != 1)
                                throw new AutomataException(AutomataExceptionKind.InternalError);

                            if (!C1.ContainsKey(move.TargetState))
                                C1[move.TargetState] = move.Label.Item2.First.OperationKind;
                            else
                                C1[move.TargetState] = C1[move.TargetState] | move.Label.Item2.First.OperationKind;
                        }
                        else
                        {
                            if (move.Label.Item2.Length > 0)
                                throw new AutomataException(AutomataExceptionKind.InternalError);

                            Q1.Add(move.TargetState);
                        }
                    }
                    #endregion
                }

                Q = Q1;
                C.Clear();
                foreach (var entry in C1)
                {
                    #region update target registers and construct set of valid counting sets
                    var c = counters[GetCounter(entry.Key).CounterId];
                    if (entry.Value == CounterOp.INCR)
                    {
                        c.Incr();
                    }
                    else if (entry.Value == (CounterOp.INCR | CounterOp.SET0))
                    {
                        c.IncrPush0();
                    }
                    else if (entry.Value == (CounterOp.INCR | CounterOp.SET1))
                    {
                        c.IncrPush1();
                    }
                    else if (entry.Value == (CounterOp.INCR | CounterOp.SET0 | CounterOp.SET1))
                    {
                        c.IncrPush01();
                    }
                    else if (entry.Value == CounterOp.SET0)
                    {
                        c.Set0();
                    }
                    else if (entry.Value == CounterOp.SET1)
                    {
                        c.Set1();
                    }
                    else if (entry.Value == (CounterOp.SET0 | CounterOp.SET1))
                    {
                        c.Set1();
                        c.Push0();
                    }
                    else
                    {
                        throw new AutomataException(AutomataExceptionKind.InternalError);
                    }
                    if (!c.IsEmpty())
                    {
                        C.Add(entry.Key);
                    }
                    #endregion
                }
            }
            if (Q.Overlaps(GetFinalStates()))
                return true;
            else
            {
                foreach (var q in C)
                {
                    if (IsFinalState(q))
                    {
                        //check that the maximum value of the counter is at least the lower bound
                        if (counters[GetCounter(q).CounterId].Max() >= GetCounter(q).LowerBound)
                            return true;
                    }
                }
                return false;
            }
        }

        private IEnumerable<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>> GetMovesFrom(List<int> states, S a, CsConditionSeq psi)
        {
            throw new NotImplementedException();
        }

        /// <summary>
        /// Creates counter minterms for the given set of counting states and input predicate.
        /// </summary>
        /// <param name="list">list of counting states, possibly empty i.e. null</param>
        /// <param name="a">input predicate</param>
        /// <returns></returns>
     /*   private IEnumerable<CsConditionSeq> GenerateCounterMinterms(ConsList<int> list, S a)
        {
            if (list == null)
                yield return CsConditionSeq.MkTrue(countingStates.Count());
            else
            {
                var a_moves = new List<Move<Tuple<Maybe<S>, Sequence<CounterOperation>>>>(GetMovesFrom(list.First, a)).ToArray();


                var incr_exists = Array.Exists(a_moves, m => m.Label.Item2.First.OperationKind == CounterOp.INCR);
                var exit_exists = Array.Exists(a_moves, m => m.Label.Item2.First.OperationKind != CounterOp.INCR);
                var i = GetCounter(list.First).CounterId;

                foreach (var seq in GenerateCounterMinterms(list.Rest, a))
                {
                    if (a_moves.Length > 0)
                    {
                        if (incr_exists && exit_exists)
                        {
                            yield return seq.Update(i, CsCondition.LOW);
                            if (!(IsSingletonCountingState(list.First) && GetCounter(list.First).LowerBound == GetCounter(list.First).UpperBound))
                                yield return seq.Update(i, CsCondition.MIDDLE);
                            yield return seq.Update(i, CsCondition.HIGH);
                        }
                      else if (incr_exists)
                        {
                            yield return seq.Update(i, CsCondition.CANLOOP);
                        }
                        else if (exit_exists)
                        {
                            yield return seq.Update(i, CsCondition.CANEXIT);
                        }
                        else
                        {
                            throw new AutomataException(AutomataExceptionKind.InternalError_GenerateCounterMinterms);
                        }
                    }
                    else
                        yield return seq;
                }
            }
        }*/

        internal CsUpdateSeq GetCounterUpdate(int q, S input, CsConditionSeq guard)
        {
            var res = CsUpdateSeq.MkNOOP(countingStates.Count());
            foreach (var mv in delta[q])
            {
                if (mv.Label.Item1.IsSomething && solver.IsSatisfiable(solver.MkAnd(mv.Label.Item1.Element, input)))
                {
                    var p = mv.TargetState;
                    if (IsCountingState(p))
                    {
                        var p_counter = GetCounter(p);
                        if (p == q)
                        {
                            #region loop
                            if (mv.Label.Item2.Length != 1)
                                throw new AutomataException(AutomataExceptionKind.InternalError);
                            else
                            {
                                var op = mv.Label.Item2[0];
                                if (guard[p_counter.CounterId].HasFlag(CsCondition.LOW) ||
                                    guard[p_counter.CounterId].HasFlag(CsCondition.MIDDLE) ||
                                    guard[p_counter.CounterId].HasFlag(CsCondition.HIGH))
                                {
                                    if (op.OperationKind == CounterOp.INCR)
                                    {
                                        res = res.Or(op.Counter.CounterId, CsUpdate.INCR);
                                    }
                                    else if (op.OperationKind == CounterOp.EXIT_SET0)
                                    {
                                        res = res.Or(op.Counter.CounterId, CsUpdate.ADD0);
                                    }
                                    else if (op.OperationKind == CounterOp.EXIT_SET1)
                                    {
                                        res = res.Or(op.Counter.CounterId, CsUpdate.ADD1);
                                    }
                                    else
                                    {
                                        throw new AutomataException(AutomataExceptionKind.InternalError);
                                    }
                                }
                            }
                            #endregion
                        }
                        else if (IsCountingState(q))
                        {
                            #region q is counting state too
                            var q_counter = GetCounter(q);
                            if (mv.Label.Item2.Length != 2)
                                throw new AutomataException(AutomataExceptionKind.InternalError);
                            else
                            {
                                var q_exit = mv.Label.Item2[0];
                                var p_set = mv.Label.Item2[1];
                                if (q_exit.Counter.CounterId != q_counter.CounterId || p_set.Counter.CounterId != p_counter.CounterId)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);

                                if (guard[q_counter.CounterId].HasFlag(CsCondition.HIGH) ||
                                    guard[q_counter.CounterId].HasFlag(CsCondition.MIDDLE))
                                {
                                    if (p_set.OperationKind == CounterOp.SET0)
                                    {
                                        res = res.Or(p_set.Counter.CounterId, CsUpdate.ADD0);
                                    }
                                    else if (p_set.OperationKind == CounterOp.SET1)
                                    {
                                        res = res.Or(p_set.Counter.CounterId, CsUpdate.ADD1);
                                    }
                                    else
                                    {
                                        throw new AutomataException(AutomataExceptionKind.InternalError);
                                    }
                                }
                            }
                            #endregion
                        }
                        else
                        {
                            #region q is non-counting state
                            if (mv.Label.Item2.Length != 1)
                                throw new AutomataException(AutomataExceptionKind.InternalError);
                            else
                            {
                                var p_set = mv.Label.Item2[0];
                                if (p_set.Counter.CounterId != p_counter.CounterId)
                                    throw new AutomataException(AutomataExceptionKind.InternalError);


                                if (p_set.OperationKind == CounterOp.SET0)
                                {
                                    res = res.Or(p_set.Counter.CounterId, CsUpdate.ADD0);
                                }
                                else if (p_set.OperationKind == CounterOp.SET1)
                                {
                                    res = res.Or(p_set.Counter.CounterId, CsUpdate.ADD1);
                                }
                                else
                                {
                                    throw new AutomataException(AutomataExceptionKind.InternalError);
                                }
                            }
                            #endregion
                        }
                    }
                }
            }
            return res;
        }
    }

    /// <summary>
    /// Dummy Boolean algebra use only for customized pretty printing of CountingAutomaton transition labels
    /// </summary>
    internal class CABA<S> : IBooleanAlgebra<Tuple<Maybe<S>, Sequence<CounterOperation>>>, IPrettyPrinter<Tuple<Maybe<S>, Sequence<CounterOperation>>>
    {
        internal SymbolicRegexBuilder<S> builder;
        public CABA(SymbolicRegexBuilder<S> builder)
        {
            this.builder = builder;
        }

        public string PrettyPrint(Tuple<Maybe<S>, Sequence<CounterOperation>> t)
        {

            if (t.Item1.IsSomething)
            {
                if (t.Item2.Length > 0)
                {
                    //char imp = SpecialCharacters.IMPLIES;
                    //char prod = SpecialCharacters.MIDDOT;
                    char prod = '/';
                    char imp = '/';


                    if (t.Item2.Length == 1)
                    {
                        return builder.solver.PrettyPrint(t.Item1.Element) + prod + t.Item2[0].ToString();
                        
                    }
                    else
                        return builder.solver.PrettyPrint(t.Item1.Element) + prod + t.Item2.ToString();
                }
                else
                    return builder.solver.PrettyPrint(t.Item1.Element);
            }
            else
            {
                string s = "";
                for (int i = 0; i < t.Item2.Length; i++)
                {
                    if (t.Item2[i].OperationKind != CounterOp.EXIT)
                        throw new AutomataException(AutomataExceptionKind.InternalError);

                    if (t.Item2[i].Counter.LowerBound > 0)
                    {
                        if (s != "")
                            s += SpecialCharacters.AND;
                        s += string.Format("{0}{1}{2}", SpecialCharacters.c(t.Item2[i].Counter.CounterId), SpecialCharacters.GEQ, t.Item2[i].Counter.LowerBound);
                    }
                }
                return (s == "" ? SpecialCharacters.TOP.ToString() : s) + SpecialCharacters.CHECKMARK;
            }
        }

        #region not implemented
        public Tuple<Maybe<S>, Sequence<CounterOperation>> False
        {
            get
            {
                throw new NotImplementedException();
            }
        }

        public bool IsAtomic
        {
            get
            {
                throw new NotImplementedException();
            }
        }

        public bool IsExtensional
        {
            get
            {
                throw new NotImplementedException();
            }
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> True
        {
            get
            {
                throw new NotImplementedException();
            }
        }

        public bool AreEquivalent(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate1, Tuple<Maybe<S>, Sequence<CounterOperation>> predicate2)
        {
            throw new NotImplementedException();
        }

        public bool CheckImplication(Tuple<Maybe<S>, Sequence<CounterOperation>> lhs, Tuple<Maybe<S>, Sequence<CounterOperation>> rhs)
        {
            throw new NotImplementedException();
        }

        public bool EvaluateAtom(Tuple<Maybe<S>, Sequence<CounterOperation>> atom, Tuple<Maybe<S>, Sequence<CounterOperation>> psi)
        {
            throw new NotImplementedException();
        }

        public IEnumerable<Tuple<bool[], Tuple<Maybe<S>, Sequence<CounterOperation>>>> GenerateMinterms(params Tuple<Maybe<S>, Sequence<CounterOperation>>[] constraints)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> GetAtom(Tuple<Maybe<S>, Sequence<CounterOperation>> psi)
        {
            throw new NotImplementedException();
        }

        public bool IsSatisfiable(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkAnd(params Tuple<Maybe<S>, Sequence<CounterOperation>>[] predicates)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkAnd(IEnumerable<Tuple<Maybe<S>, Sequence<CounterOperation>>> predicates)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkAnd(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate1, Tuple<Maybe<S>, Sequence<CounterOperation>> predicate2)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkDiff(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate1, Tuple<Maybe<S>, Sequence<CounterOperation>> predicate2)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkNot(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkOr(IEnumerable<Tuple<Maybe<S>, Sequence<CounterOperation>>> predicates)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkOr(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate1, Tuple<Maybe<S>, Sequence<CounterOperation>> predicate2)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> MkSymmetricDifference(Tuple<Maybe<S>, Sequence<CounterOperation>> p1, Tuple<Maybe<S>, Sequence<CounterOperation>> p2)
        {
            throw new NotImplementedException();
        }

        public string PrettyPrint(Tuple<Maybe<S>, Sequence<CounterOperation>> t, Func<Tuple<Maybe<S>, Sequence<CounterOperation>>, string> varLookup)
        {
            throw new NotImplementedException();
        }

        public string PrettyPrintCS(Tuple<Maybe<S>, Sequence<CounterOperation>> t, Func<Tuple<Maybe<S>, Sequence<CounterOperation>>, string> varLookup)
        {
            throw new NotImplementedException();
        }

        public Tuple<Maybe<S>, Sequence<CounterOperation>> Simplify(Tuple<Maybe<S>, Sequence<CounterOperation>> predicate)
        {
            throw new NotImplementedException();
        }
        #endregion
    }
}
