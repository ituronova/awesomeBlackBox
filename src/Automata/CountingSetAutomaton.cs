using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Automata.BooleanAlgebras;
using System.Runtime.CompilerServices;
using System.IO;
using System.Text.RegularExpressions;
using System.Collections;

namespace Microsoft.Automata
{   
    /// <summary>
    /// Counting-set Automaton Optimized
    /// </summary>
    public class CsAutomatonOpt<S> : Automaton<CsLabel<S>>
    {
        List<List<int>> ssc;
        int[][] transitionTable;
        int[][] cycleTable;
        public double[,] weightTable;
        public int[][] successors;
        public int[][] revsuccessors;
        public bool[] coolNodes;
        Tuple<CsUpdate[], int>[][] transInfoTable;
        Dictionary<int, Tuple<CsUpdate[], int>>[] tInfoTable;
        // CsConditionSeq[] finalStateInfoTable;
        int[][] finalCounters;
        public string str = "";
        PowerSetStateBuilder stateBuilder;
        Dictionary<int, ICounter> countingStates;
        public ICharAlgebra<S> inputAlgebra;
        //CsAlgebra<S> productAlgebra;
        //int[] origFinalStates;
        int[][] usedCounters;
        public int[][][] updatedCounters;
        public int[][][] usefulCounters;
        public List<int>[] stateCounters;
        public int limit = 256;
        public double[] mapStateToCycles;
        public int[] precomputed;
        public ICounter[] counters;
        Dictionary<int, int> mapStates;
        //int[] finalCounterSet;
        public bool[] finalSet;
        public BasicCountingSet[] cs;
        public int currentState;
        public int[] sizeCA;
        public ValueTuple<int,BasicCountingSet[]> currentConf;
        public int up = 0;
        public int still = 0;
        public int done = 0;
        public int broken = 0;
        public int part = 0;
        public int finished = 0;
        public List<CsUpdate>[] updateTree;
        public int[] minterms;
        public S[] minSymbols;
        public List<int>[] elemCS;
        public cop[][] deltaPre;
        bool A_startAnchor = false;
        public bool A_endAnchor = false;
        public bool addedWord;
        public int[][] configs;
        private double[] distance;
        private int[] pre;
        public bool[] finalState;
        public Dictionary<conf, int> mapConf;
        public Dictionary<int, conf> mapConfStates;
        public List<Tuple<int, int>> confAut;
        public SortedList<string, Object> unvisited;
        public int countUnvisited;
        public string dotFile;
        public int found;
        public int line;
        public int visited;
        public int countConf;
        public int countSucc = 0;


        public class ConfEqualityComparer : IEqualityComparer<conf>
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public int GetHashCode(conf obj)
            {
                return base.GetHashCode();
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public bool Equals(conf c1, conf c2)
            {
                if (c1.state == c2.state)
                {
                    if (c1.basicSet != null) // if there is a counter
                    {
                        for (int i = 0; i < c1.counters; i++)
                        {
                            if (!c1.basicSet[i].Equals(c2.basicSet[i]))
                                return false;
                        }
                    }
                    return true;
                }
                return false;
            }
        }    
   

        public class conf
        {
            readonly int State;
            readonly int Counters;
            readonly symbConf[] BasicSet;
    
            public ValueTuple<int, BasicCountingSet[]> RecoverCS(int mapState)
            {
                BasicCountingSet[] bs = null;
                if (this.counters != 0)
                {
                    bs = new BasicCountingSet[this.BasicSet.Length];
                    for (int i = 0; i < this.BasicSet.Length; i++)
                        bs[i] = new BasicCountingSet(this.BasicSet[i]);
                }
                return ValueTuple.Create<int, BasicCountingSet[]>(state, bs);
            }

            public string ToString(double distance, int size, double weight)
            {
                string s = State + " | ";
                for(int i = 0; i < BasicSet.Count(); i++)
                {
                    s += BasicSet[i].ToString();
                }
                s += " | Dist: " + distance + " | Size: " + size + " | Weight: " + weight;
                return s;
            }

            /*   public BasicCountingSet[] cs
               {
                   get
                   {
                       return CS;
                   }
               }*/
                public symbConf[] basicSet
                {
                    get
                    {
                        return BasicSet;
                    }
                }

            
            public int state
            {
                get
                {
                    return State;
                }
            }

            public int counters
            {
                get
                {
                    return Counters;
                }
            }

            public bool IsEmpty()
            {
                if (state == 0)
                    return true;
                else return false;
            }

            public conf(int state, BasicCountingSet[] cSet, ICounter[] counters)
            {
                this.State = state;
                this.Counters = counters.Length;
                if (cSet != null)
                {
                    this.BasicSet = new symbConf[Counters];
                    for (int c = 0; c < Counters; c++)
                    {
                        this.BasicSet[c] = new symbConf(cSet[c], counters[c]);
                    }
                }
            }

            public conf(conf conf, ICounter[] counters)
            {
                this.State = conf.State;
                this.Counters = counters.Length;
                if (conf.BasicSet != null)
                {
                    //this.CS = new BasicCountingSet[Counters];
                    this.BasicSet = new symbConf[Counters];
                    for (int c = 0; c < Counters; c++)
                    {
                        this.BasicSet[c] = new symbConf(conf.BasicSet[c]);
                    }
                }
            }
            public override bool Equals(object obj)
            {
                var c = (conf)obj;
                if (c.state == this.state)
                {
                    for (int i = 0; i < Counters; i++)
                    {
                        if (!c.BasicSet[i].Equals(this.BasicSet[i]))
                            return false;
                    }
                    return true;
                }
                return false;
            }

            public override int GetHashCode()
            {
                return base.GetHashCode();
            }

        }

        public int MaxElemCS
        {
            get
            {
                int max = -1;
                for (int i = 0; i < this.cntCount; i++)
                {
                    if (this.elemCS == null)
                        return -1;
                    if (max < this.elemCS[i].Max())
                            max = this.elemCS[i].Max();       
                }
                return max;
            }
        }

        public int SetWeightOfState(int state, BasicCountingSet[] cs)
        {
            int size = 0;
            for (int i = 0; i < this.cntCount; i++)
            {
                var elems = cs[i].CountElements();
                if (this.configs[state][i] > 0)
                    size += elems;
            }
            return size;
        }

        public bool Better(int c1, int c2, double d1, double d2)
        {
            /* if (finalState[c1] == finalState[c2])
             {
                 if (d1 > d2)    // compare weights of states
                     return true;
                 else if (d1 == d2)
                 {
                     if (sizeCA[c1] >= sizeCA[c2])
                         return true;
                 }                  
             }
             else if (finalState[c2])
             {
                 return true;
             }*/
            Random r = new Random();
            int rInt = r.Next(0, 100);
            if (rInt > 50)
                return true;
            return false;
        }

        public int MaxCounter
        {
            get
            {
                int max = -1;
                for (int i = 0; i < this.cntCount; i++)
                {
                    if (max < this.counters[i].UpperBound)
                        max = this.counters[i].UpperBound;
                }
                return max;
            }
        }

        public int SumCounter
        {
            get
            {
                int sum = 0;
                for (int i = 0; i < this.cntCount; i++)
                {
                    sum += this.counters[i].UpperBound;
                }
                return sum;
            }
        }

        public double AvrgCS
        {
            get
            {
                double avrg = 0;
                for (int i = 0; i < this.cntCount; i++)
                {
                    if (this.elemCS == null)
                        return -1;
                    for (int j = 0; j < this.elemCS[i].Count(); j++)
                        avrg += this.elemCS[i][j];
                }
                if (this.elemCS != null)
                {
                    if(this.elemCS.Length != 0)
                        avrg /= this.elemCS[0].Count;
                }                    
                else
                    Console.WriteLine("Error: Division by zero.");
                return avrg;
            }
        }

        public int TransCount
        {
            get { return this.GetAllMoves().Count; }
        }


        /// <summary>
        /// Underlying Cartesian product algebra
        /// </summary>
        /*public CsAlgebra<S> ProductAlgebra
        {
            get
            {
                return productAlgebra;
            }
        }*/

        static void Init<T>(T[] array, T defaultVaue)
        {
            if (array == null)
                return;
            for (int i = 0; i < array.Length; i++)
            {
                array[i] = defaultVaue;
            }
        }

        public void InitCycleTable()
        {
            this.weightTable = new double[this.cntStates + 1, this.cntStates + 1];
            this.successors = new int[this.cntStates + 1][];
            this.revsuccessors = new int[this.cntStates + 1][];
            var reverseList = new List<int>[this.cntStates + 1];
            for (int i = this.cntStates; i >= 1 ; i--)
            {
                List<int> sucList = new List<int>();
                for (int j = 1; j < this.cntStates + 1; j++)
                {
                    if (this.deltaPre[i][j].IsEmpty())  // skip edges with EXIT
                        continue;
                    if (this.GetMoveFromTo(i, j) != null)
                    {
                        // reverse table
                        if (reverseList[j] == null)
                            reverseList[j] = new List<int> {i};
                        else
                            reverseList[j].Add(i);
                        // set weight to 0
                        weightTable[i,j] = 0;
                        // successors
                        sucList.Add(j);                       
                    }
                    else
                        weightTable[i,j] = -double.MaxValue;
                }
                this.successors[i] = sucList.ToArray();

            }
            for (int j = 1; j < this.cntStates + 1; j++)
            {
                if(reverseList[j] != null)
                    this.revsuccessors[j] =  reverseList[j].ToArray();
            }
            //CompareDelta();
        }

        public int [] UpdateSucc(int max)
        {
            int[] size = new int[max];
            for(int i = 0; i < max; i++)
            {
                size[i] = this.ssc[i].Count();
                for(int j = 0; j < size[i]; j++)
                {
                    var node = ssc[i][j];
                    List<int> res = (successors[node].Intersect(this.ssc[i])).ToList();
                    var a = new List<int>();
                    for (int d = 0; d < res.Count(); d++)
                    {
                        var ops = this.deltaPre[node][res[d]];
                        if (ops.Evel)
                        {
                            continue;
                        }
                        else
                            a.Add(res[d]);
                    }                    
                    this.successors[node] = a.ToArray();
                }
            }
            return size;
        }

        private Random rand = new Random();

        public double GetRandomNumber(double minimum, double maximum)
        {
            return rand.NextDouble() * (maximum - minimum) + minimum;
        }


        public int GetRandomState()
        {
            return rand.Next(1, this.cntStates);
        }

        public int GetRandomCut(int max)
        {
            return rand.Next(0, max);
        }

        private int[] AllowedValues = new int[] { 1, 2, 4};
        private int GetRandomFlag()
        {
            return AllowedValues[rand.Next(AllowedValues.Length)];
        }

        public CsAutomatonOpt(ICharAlgebra<S> algebra, Automaton<CsLabel<S>> aut, int countMoves, PowerSetStateBuilder stateBuilder, Dictionary<int, List<Tuple<CsConditionSeq, Tuple<CsUpdate[], int>>>[]> transTable, int countStates, int[] finalStatethis, ICounter[] counters, int countCounters, int[] precomputed, int[] minterms, Dictionary<int, int> mapping, Dictionary<int, HashSet<int>> finalCounters, Dictionary<int, HashSet<int>[]> updatedCounters, Dictionary<int, HashSet<int>> usedCounters, S[] minSymbols, Dictionary<int, int[]> configs) : base(aut)
        {
            this.stateBuilder = stateBuilder;
            this.currentState = -1;
            this.inputAlgebra = algebra;
            this.cntStates = countStates;
            this.cycleTable = new int[cntStates + 1][];
            this.finalSet = new bool[this.cntStates + 1];
            this.minterms = minterms;
            this.minSymbols = minSymbols;
            for (int i = 0; i < this.cntStates + 1; i++)
            {
                this.cycleTable[i] = new int[this.cntStates + 1];
                for (int j = 0; j < this.cntStates + 1; j++)
                    this.cycleTable[i][j] = -Int16.MaxValue;
            }
            for (int i = 0; i < finalStatethis.Length; i++)
            {
                this.finalSet[finalStatethis[i]] = true;
            }
            this.configs = new int[this.cntStates+1][];
            foreach(var item in configs)
            {
                this.configs[item.Key] = item.Value;
            }

            this.precomputed = precomputed;
            this.counters = counters;
            this.cntCount = countCounters;
            this.mapStates = mapping;
            int index = 1;
            this.transitionTable = new int[this.cntStates + 1][];
            this.transInfoTable = new Tuple<CsUpdate[], int>[countMoves + 1][];
            this.tInfoTable = new Dictionary<int, Tuple<CsUpdate[], int>>[countMoves + 1];
            // set of final counters for each final state
            this.finalCounters = new int[this.cntStates + 1][];
            // updated counters for target state
            this.updatedCounters = new int[this.cntStates + 1][][];
            this.usedCounters = new int[this.cntStates + 1][];
            this.usefulCounters = new int[this.cntStates + 1][][];
            this.stateCounters = new List<int>[this.cntStates + 1];
            
            for (int i = 1; i <= this.cntStates; i++)
            {
                this.updatedCounters[i] = new int[minterms.Length][];
                this.usefulCounters[i] = new int[minterms.Length][];
                this.stateCounters[i] = new List<int>();
                if (this.finalSet[i])
                    this.finalCounters[i] = finalCounters[i].ToArray();
                var uc = usedCounters[i].ToArray();
                transitionTable[i] = new int[minterms.Length];
                this.usedCounters[i] = uc;
                for (int j = 0; j < minterms.Length; j++)
                {
                    var minterm = minterms[j];
                    var moves = transTable[i][j];
                    if (moves == null)
                        continue;
                    this.updatedCounters[i][minterm] = updatedCounters[i][minterm].ToArray();

                    Tuple<CsUpdate[], int>[] condTable = null;
                    condTable = new Tuple<CsUpdate[], int>[(long)Math.Pow(2, this.usedCounters[i].Length * 2)];                    

                    List<int> ucounters = new List<int>();
                    foreach(var g in this.usedCounters[i])
                    {
                       if (!this.updatedCounters[i][minterm].Contains(g))
                        {
                            ucounters.Add(g);
                        }
                    }
                    this.usefulCounters[i][minterm] = ucounters.ToArray();
                    this.stateCounters[i] = this.stateCounters[i].Union(this.usedCounters[i]).ToList();
                    for (int m = 0; m < moves.Count(); m++)
                    {
                        var move = moves[m];
                        // no condition on counter
                        // updated counters for target
                        if (this.updatedCounters[i][minterm].Length == 0)
                            transitionTable[i][minterm] = move.Item2.Item2;
                        else
                        {
                            int condIndex = -1;
                            condIndex = move.Item1.CountIndex(this.usedCounters[i]);
                            condTable[condIndex] = move.Item2;
                        }
                    }
                    if (this.updatedCounters[i][minterm].Length != 0)
                    {
                        transitionTable[i][minterm] = -index;
                        transInfoTable[index] = condTable;
                        index++;
                    }
                }
            }
            if (this.cntCount != 0)
            {   // initialize counting sets
                this.cs = new BasicCountingSet[cntCount];
                for (int i = 0; i < this.cntCount; i++)
                {
                    this.cs[i] = new BasicCountingSet(this.counters[i]);    // initialization to 0   
                }
            }
            // initial state
            this.currentState = this.InitialState;
        }

        /// <summary>
        /// Gets the number of counters.
        /// All counters are numbered from 0 to NrOfCounters-1.
        /// </summary>
        /* public override int NrOfCounters
         {
             get
             {
                 return this.countingStates.Count;
             }

         }*/
        int GetOriginalInitialState()
        {
            foreach (var q0 in stateBuilder.GetMembers(InitialState))
                return q0;
            throw new AutomataException(AutomataExceptionKind.SetIsEmpty);
        }
        
        bool __hidePowersets = false;
        internal bool __debugmode = false;

        public void ShowGraph(string name = "CsAutomaton", bool debumode = false, bool hidePowersets = false)
        {
            __hidePowersets = hidePowersets;
            __debugmode = debumode;
            base.ShowGraph(name);
        }

        public void SaveGraph(string name = "CsAutomaton", bool debumode = false, bool hidePowersets = false)
        {
            __hidePowersets = hidePowersets;
            __debugmode = debumode;
            base.SaveGraph(name);
        }


        Dictionary<int, string> stateDescr = new Dictionary<int, string>();

        /// <summary>
        /// Describe the state information, including original states if determinized, as well as counters.
        /// </summary>
        public override string DescribeState(int state)
        {
            string s;

            if (!stateDescr.TryGetValue(state, out s))
            {
                s = SpecialCharacters.S(stateDescr.Count);
                stateDescr[state] = s;
            }

            int stateIndex = mapStates.FirstOrDefault(x => x.Value == state).Key;
            var mems = new List<int>(stateBuilder.GetMembers(stateIndex));
            mems.Sort();
            if (!__hidePowersets)
            {
                s += "\n" + "{";
                foreach (var q in mems)
                {
                    if (!s.EndsWith("{"))
                        s += ",";
                    s += SpecialCharacters.q(q);
                }
                s += "}";
            }
            var state_counters = GetCountersOfState(state);
            if (state_counters != null)
            {
                var state_counters_list = new List<int>(state_counters);
                state_counters_list.Sort();
                foreach (var c in state_counters_list)
                {
                    s += "\n";
                    s += "(" + SpecialCharacters.c(c) + ")";
                    //s += "(" + counters[c].LowerBound + 
                    //    SpecialCharacters.LEQ + SpecialCharacters.c(c) + SpecialCharacters.LEQ + counters[c].UpperBound + ")";
                    if (finalSet[c])
                    {
                        s += SpecialCharacters.XI_LOWERCASE + SpecialCharacters.ToSubscript(c);
                        s += SpecialCharacters.CHECKMARK;
                    }
                }
            }
            if (mapStateToCycles != null)
            {
                if (mapStateToCycles[state] != -Int64.MaxValue)
                {
                    s += "weight: " + mapStateToCycles[state];
                }
            }
            return s;
        }

        /// <summary>
        /// Describe if the initial state is associuated with a counter, if so then set it to {0}
        /// </summary>
        public override string DescribeStartLabel()
        {
            var initcounters = new List<int>();
            for (int i = 0; i < updatedCounters[InitialState].Length; i++)
            {
                if (updatedCounters[InitialState][i] != null)
                    initcounters = initcounters.Union(updatedCounters[InitialState][i]).ToList();
            }
            if (initcounters.Count != 0)
            {
                var c = initcounters[0];
                return string.Format("{0}={{0}}", SpecialCharacters.c(c));
            }
            else
                return "";
        }

        public override string DescribeLabel(CsLabel<S> lab)
        {
            return lab.ToString(__debugmode);
        }

        public void SpreadWeight(bool verbose)
        {
            bool[] shortestPathTreeSet = new bool[this.cntStates+1];    

            for (int count = 1; count < this.cntStates + 1; ++count)
            {
                int u = MaximumWeight(shortestPathTreeSet, this.cntStates + 1);
                shortestPathTreeSet[u] = true;

                for (int v = 1; v < this.cntStates + 1; ++v)
                {
                    if (!shortestPathTreeSet[v] && !deltaPre[v][u].IsEmpty() && mapStateToCycles[u] - 0.5 > mapStateToCycles[v])
                    {
                        mapStateToCycles[v] = mapStateToCycles[u] - 0.5;
                    }
                }
            }            
        }      

        public bool[] GetSSC(int i)
        {
            bool[] set = new bool[this.cntStates + 1];
            for (int j = 1; j < this.cntStates + 1; j++)
            {
                if (ssc[i].Contains(j))
                {
                    set[j] = true;
                }
            }
            return set;
        }

        public void WeightCycles(bool verbose)
        {
            mapStateToCycles = new double[this.cntStates + 1];
            if (verbose)
                Console.WriteLine("Initialization of edges done.");
           // initialization of table of weights
            this.InitCycleTable();
            // compute all SSCs
            this.Kosaraju();
            var number = this.ssc.Count();
          /*  for (int i = 1; i < this.cntStates+1; i++)
            {
                Console.Write("\nState " + i + ": ");
                for (int j = 0; j < this.successors[i].Length; j++)
                    Console.Write(successors[i][j] + " ");
            }
            Console.WriteLine("Update");*/
            var size = this.UpdateSucc(number);
           
           /* for (int i = 1; i < this.cntStates + 1; i++)
            {
                Console.Write("\nState " + i + ": ");
                for (int j = 0; j < this.successors[i].Length; j++)
                    Console.Write(successors[i][j] + " ");
            }*/
            // Console.WriteLine("Number of SCC: " + number);
          /*  for (int i = 0; i < number; i++)
            {
                Console.WriteLine("Size: " + size[i]);
                for (int k = 0; k < this.ssc[i].Count(); k++)
                    Console.Write(this.ssc[i][k] + " ");
                Console.Write("\n");
            }*/
            for (int i = 0; i < number; i++)
            {
                // bool[] isVisited = new bool[this.cntStates + 1];
                // get SSC for the state i            
                for (int k = 0; k < size[i]; k++)
                {
                    var startNode = this.ssc[i][k];
                    if (!coolNodes[startNode])  // skip node that has no outgoing edge with ADD/INCR0/INCR1
                        continue;
                    //Console.WriteLine("searching for node: " + startNode);

                    // find all cycles started in state i
                    this.cycles = SimpleList<List<int>>.Empty;
                    var nodePath = SimpleList<int>.Empty;
                    bool[] isVisited = new bool[cntStates+1];
                    this.FindAllCycles(startNode);
                      
                   //Console.WriteLine("Number of cycles for node " + startNode + ": "+ numberOfCycles);
                    numberOfCycles = 0;
                    // if there is a cycle
                    if (cycles != null)
                    {
                        int[] bestCycle = null;
                        // for each cycle compute its weight
                        var max = 0.0;
                        int count = 0;
                      
                            foreach (var simpleCycle in cycles)
                            {
                                var cycle = simpleCycle.ToArray();
                                count++;
                                double w = -1.0;
                                w = this.ComputeWeight(cycle);
                                 /*   Console.Write("Cycle: ");
                                    for (int b = 0; b < cycle.Length; b++)
                                        Console.Write(cycle[b] + " ");
                                    Console.WriteLine("\nw: " + w);*/
                               
                                if (w > max)
                                {
                                    bestCycle = simpleCycle.ToArray(); 
                                    max = w;                                    
                                }
                            }
                        // remember the cycle for state i
                        if (max > mapStateToCycles[startNode])
                        {
                            this.mapStateToCycles[startNode] = max;
                        }
                       /* if (bestCycle != null)
                        {
                            Console.WriteLine("Cycle: ");
                            for (int b = 0; b < bestCycle.Length; b++)
                                Console.WriteLine(bestCycle[b] + " ");
                            Console.WriteLine("\nw: " + max);
                        }*/
                        // distribute weight along the cycle
                        if (bestCycle != null)
                        {
                            // TODO: here is error
                            for (int b = 1; b < bestCycle.Length - 1; b++)
                            {
                                if (max > mapStateToCycles[bestCycle[b]])
                                {
                                    mapStateToCycles[bestCycle[b]] = max;
                                }
                            }
                           //Console.WriteLine("\nw: " + max);
                        }
                    }
                }
            }
        }

 

        
        /// <summary>
        /// Get the active counters associated with the given state.
        /// The set is empty if this state is not asscociated with any counters.
        /// </summary>
        public List<int> GetCountersOfState(int state)
        {
            var list = new List<int>();
            for (int i = 0; i < updatedCounters[state].Length; i++)
            {
                if (updatedCounters[state][i] != null)
                    list.Union(updatedCounters[state][i]);
            }
            return list;
        }

        bool IsCountingState(int state)
        {
            if (this.countingStates.Keys.Contains(state))
                return true;
            return false;
        }

        /* List<S> GetMinterms(List<Move<CsLabel<S>>> moves)
         {
             var minterms = new List<S>();
             minterms = Array.ConvertAll(moves.ToArray(), move => move.Label.InputGuard).ToList();
             return minterms;
         }*/

        // filter moves according to symbolic minterm, return tuples - guard, update, target
        /*  List<Tuple<CsConditionSeq, CsUpdateSeq, int>> FilterMoves(List<Move<CsLabel<S>>> moves, S minterm, out int noncondTarget)
          {
              //var pred = productAlgebra.MkPredicate(minterm, productAlgebra.TrueCsConditionSeq);
              var list = new List<Tuple<CsConditionSeq, CsUpdateSeq, int>>();
              noncondTarget = -1;
              int nocond = 0;
              for (int i = 0; i < moves.Count(); i++)
              {
                  var move = moves[i];
                  if (inputAlgebra.EvaluateAtom(minterm, move.Label.Symbol))
                  {
                      // TODO: handle NOOP
                      if (move.Label.Updates.IsNOOP)//&& move.Label.Guard.Empty == 1)
                      {
                          noncondTarget = moves[i].TargetState;
                          nocond++;
                      }
                      list.Add(Tuple.Create(moves[i].Label.Guard, moves[i].Label.Updates, moves[i].TargetState));
                  }
              }
              if (nocond > 1)
                  return list;
              if (nocond == list.Count())  // if all moves are without update
                  return null;
              // return transition info
              return list;
          }*/

        private BasicCountingSet[] InitializeCS()
        {
            var cs = new BasicCountingSet[cntCount];
            for (int i = 0; i < cntCount; i++)
            {
                cs[i] = new BasicCountingSet(this.counters[i]);    // initialization to 0   
            }
            return cs;
        }


        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int CheckFinalCondition()
        {
            var fc = finalCounters[currentState];
            if (fc.Length == 0)
                return 0;
            for (int i = 0; i < fc.Length; i++)
            {
                if (cs[fc[i]].flag > (int)CsCondition.LOW)
                    return 0;
            }
            return 1;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int CheckFinalConditionWhileGen()
        {
            var fc = finalCounters[currentConf.Item1];
            if (fc.Length == 0)
                return 0;
            for (int i = 0; i < fc.Length; i++)
            {
                if(this.A_endAnchor)
                {
                    if(currentConf.Item2[fc[i]].Max() >= currentConf.Item2[fc[i]].upperBound)
                        return 0;
                }
                else if (currentConf.Item2[fc[i]].flag >= (int)CsCondition.MIDDLE)
                    return 0;
            }
            return 1;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int CheckFinalConditionWhileGen(ValueTuple<int, BasicCountingSet[]> conf)
        {
            var fc = finalCounters[conf.Item1];
            if (fc.Length == 0)
                return 0;
            for (int i = 0; i < fc.Length; i++)
            {
                if (conf.Item2[fc[i]].flag >= (int)CsCondition.MIDDLE)
                    return 0;
            }
            return 1;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int CheckFinalConditionWhileGen(conf conf)
        {
            var fc = finalCounters[conf.state];
            if (fc.Length == 0)
                return 0;
            for (int i = 0; i < fc.Length; i++)
            {
               if (conf.basicSet[fc[i]].Flag() >= (int)CsCondition.MIDDLE)
                return 0;
            }
            return 1;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void InitState()
        {
            if (this.cntCount != 0)
            {   // initialize counting sets
                this.cs = this.InitializeCS();
            }
            // initial state
            this.currentState = InitialState;
        }

        public int InitStateWithCS()
        {
            // initialize counting sets
            this.cs = this.InitializeCS();
            // initial state
            this.currentState = InitialState;
            return 0;
        }


        bool CompareOperations(cop op1, cop op2)
        {
            var flagI = 0;
            var flagA = 0;
            if (op1.IsEmpty())
                return true;
            for (int c = 0; c < this.cntCount; c++)
            {
                if (op1.IsEmpty(c))
                    return true;
                if (op2.Get(c, 2) != 0)
                    return false;
                // ADD
                if (op1.Get(c, 0) < op2.Get(c, 0))
                    flagA += 1;
                // ADD
                if (op1.Get(c, 0) > op2.Get(c, 0))
                    flagA -= 1;
                // INCR
                if (op1.Get(c, 1) < op2.Get(c, 1))
                    flagI += 1;
                // INCR
                if (op1.Get(c, 1) > op2.Get(c, 1))
                    flagI -= 1;
            }
            if (flagA > 0)          
                return true;
            if (flagA == 0)
            {
                if (flagI > 0)
                    return true;
            }
            return false;
        }

        private cop GetOps(CsUpdateSeq updates, int s)
        {
            cop operations = new cop(this.cntCount);

            if (updates != null)
            {
                for (int c = 0; c < this.cntCount; c++)
                {
                    switch (updates[c])
                    {
                        case CsUpdate.ADD0:
                            operations.add(c, 0, 1);
                            operations.makeItCool();    // update adds item to CS
                            break;
                        case CsUpdate.ADD1:
                            operations.add(c, 0, 1);
                            operations.makeItCool();
                            break;
                        case CsUpdate.INCR:
                            operations.add(c, 1, 1);
                            break;
                        case CsUpdate.INCR0:
                            operations.add(c, 0, 1);
                            operations.add(c, 1, 1);
                            operations.makeItCool();
                            break;
                        case CsUpdate.INCR1:
                            operations.add(c, 0, 1);
                            operations.add(c, 1, 1);
                            operations.makeItCool();
                            break;
                        case CsUpdate.INCR0_EXIT:
                            operations.add(c, 0, 1);
                            operations.add(c, 1, 1);
                            operations.add(c, 2, 1);
                            operations.makeItEvel();
                            break;
                        case CsUpdate.INCR1_EXIT:
                            operations.add(c, 0, 1);
                            operations.add(c, 1, 1);
                            operations.add(c, 2, 1);
                            operations.makeItEvel();
                            break;
                        case CsUpdate.EXIT:
                            operations.add(c, 2, 1);
                            operations.makeItEvel();    // update contains EXIT
                            break;
                        case CsUpdate.NOOP:
                            if (this.stateCounters[s].Contains(c))
                            {
                                operations.add(c, 2, 1);  // EXIT
                                operations.makeItEvel();
                            }
                            break;
                    }
                }
            }
            return operations;
        }

        public struct cop
        {
            int[][] ops;
            bool interesting;
            bool evel;

            // update adds item to CS
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void makeItCool()
            {
                interesting = true;
                return;
            }

            // update adds item to CS
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public void makeItEvel()
            {
                evel = true;
                return;
            }

            public bool Interesting
            {
                get
                {
                    return interesting;
                }
            }

            public bool Evel
            {
                get
                {
                    return evel;
                }
            }

            public override string ToString()
            {
                string s = "";

                if (this.IsEmpty())
                    return "empty\n";
                s += "[ "; 
                for (int i = 0; i < ops.Length; i++)
                {
                    s += "[ ";
                    for(int j = 0; j < ops[i].Count(); j++)
                    {
                        s += ops[i][j];
                    }
                    s += " ]";
                }
                s += " ] ";
                if (this.interesting)
                    s += "cool";
                return s;
            }
            public bool IsEmpty()
            {
                if (ops == null)
                    return true;
                return false;
            }

            public void Add(int c, int x, int value)
            {
                ops[c][x] += value;
            }

            public void Subb(int c, int x, int value)
            {
                ops[c][x] -= value;
            }

            public void Add(cop cp, int cnt)
            {
                if (this.IsEmpty())
                    this.ops = cp.Get();
                if (!cp.IsEmpty())
                {
                    for (int c = 0; c < cnt; c++)
                    {
                        if (!cp.IsEmpty(c))
                        {
                            for (int i = 0; i < 3; i++)
                            {
                                this.ops[c][i] += cp.Get(c, i);
                            }
                        }
                    }
                }
            }

            public void Subb(cop cp, int cnt)
            {
                if (!cp.IsEmpty())
                {
                    for (int c = 0; c < cnt; c++)
                    {
                        if (!cp.IsEmpty(c))
                        {
                            for (int i = 0; i < 3; i++)
                            {
                                this.ops[c][i] -= cp.Get(c, i);
                            }
                        }
                    }
                }
            }

            public bool IsEmpty(int x)
            {
                if (ops[x] == null)
                    return true;
                return false;
            }

            public int[][] Get()
            {
                return ops;
            }
            public int Get(int x, int y)
            {
                return ops[x][y];
            }

            public cop(int size)
            {
                ops = new int[size][];
                for (int i = 0; i < size; i++)
                {
                    ops[i] = new int[] { 0, 0, 0 };
                }
                this.interesting = false;
                this.evel = false;
            }

            public cop(cop cp, int size)
            {
                ops = new int[size][];
                for (int i = 0; i < size; i++)
                {
                    ops[i] = new int[] { cp.Get(i, 0), cp.Get(i, 1), cp.Get(i, 2) };
                }
                this.interesting = false;
                this.evel = false;
            }

            public void add(int x, int y, int v)
            {
                ops[x][y] = v;
            }

            public int GetSize()
            {
                return ops.Count();
            }

            public int GetSize(int i)
            {
                return ops[i].Count();
            }

            public int GetItem(int x, int y)
            {
                return ops[x][y];
            }

        }


        private void CompareDelta()
        {

            for (int i = 1; i < this.cntStates+1; i++)
            {
                for (int j = 0; j < this.cntStates + 1; j++)
                {
                    if (this.deltaPre[i][j].IsEmpty())
                    {
                        if (successors[i] == null)
                            continue;
                        if (successors[i].Contains(j))
                        {
                            Console.WriteLine(i + "->" + j + " successor is there.");
                        }
                    }
                    if (!successors[i].Contains(j))
                    {
                        if(!this.deltaPre[i][j].IsEmpty()) 
                            Console.WriteLine(i + "->" +j+" operation is there.");
                    }

                }
            }
        }

        public void Preprocessing(string rgx)
        {
            // check anchores
            if (rgx[0] == '^')
                this.A_startAnchor = true;
            if (rgx[rgx.Length - 1] == '$')
                this.A_endAnchor = true;

            int size = this.delta.Count();
            coolNodes = new bool[size + 1];    // nodes with outgoing edge with update increasing size of CS
            this.deltaPre = new cop[size + 1][];
            for (int i = 1; i <= size; i++)
            {
                this.deltaPre[i] = new cop[this.cntStates + 1];
                
                for (int j = 0; j < this.delta[i].Count(); j++)
                {
                    var succ = this.delta[i][j];
                    var ops = this.GetOps(succ.Label.Updates, i);
                    if (ops.Interesting)
                    {
                        coolNodes[i] = true;
                    }
                    
                    if (deltaPre[i][succ.TargetState].IsEmpty() || CompareOperations(deltaPre[i][succ.TargetState], ops))
                        deltaPre[i][succ.TargetState] = ops;   
                }
            }
        }

        public bool HasMoreThanOneEdge(int s)
        {
            for (int i = 1; i < this.cntStates + 1; i++)
            {
                if(!this.deltaPre[i][s].IsEmpty())
                {
                    return true;
                }
            }
            return false;
        }

        public bool HasTwoIncommingEdges(int s)
        {
            int e = 0;
            for (int i = 1; i < this.cntStates + 1; i++)
            {
                if (!this.deltaPre[i][s].IsEmpty())
                {
                    e++;
                    if (e > 1)
                        return true;
                }
            }
            return false;
        }

      /*  public bool[] GetSCC(int s)
        {
            bool[] set = new bool[this.cntStates+1];
            for (int i = 0; i < this.ssc.Count(); i++)
            {
                if (ssc[i].Contains(s))
                {
                    for(int j = 1; j < this.cntStates+1; j++)
                    {
                        if(ssc[i].Contains(j))
                        {
                            set[j] = true;
                        }
                    }
                    return set;
                }
                    
            }
            return null;
        }*/

        /// <summary>
        /// Kosaraju's strongly connected components algorithm
        /// </summary>
        public void Kosaraju()
        {
            var stack = new Stack<int>();
            var visited = new bool[this.cntStates + 1];

            Action<int> Visit = null;
            Visit = (u) =>
            {
                visited[u] = true;
                stack.Push(u);
                for (int i = 0; i < this.successors[u].Length; i++)
                {
                    var succ = this.successors[u][i];
                    if(!this.A_endAnchor)
                        if (IsFinalState(u) && IsFinalState(succ))
                            continue;
                    if (!visited[succ])
                        Visit(succ);
                }
            };

            var cs = new List<int>();
            Action<int, int> Assign = null;
            Assign = (u, root) =>
            {
                if (!visited[u])
                {
                    if (u == root)
                    {
                        // Console.Write("SCC: ");
                        cs = new List<int>();
                    }
                    cs.Add(u);
                    visited[u] = true;
                    //Console.Write(u + " ");

                    if (this.revsuccessors[u] == null)
                    {
                        ssc.Add(cs);
                        return;
                    }
                    for (int i = 0; i < this.revsuccessors[u].Length; i++)
                    {
                        var succ = this.revsuccessors[u][i];
                        if (!visited[succ])
                            Assign(succ, root);
                    }
                    if (u == root)
                    {
                        //   Console.WriteLine();
                        ssc.Add(cs);
                    }
                }
            };
            Visit(1);
            visited = new bool[this.cntStates + 1];
            ssc = new List<List<int>>();
            stack = this.Reverse(stack);
            while (stack.Count != 0)
            {
                var sc = new List<int>();
                var node = stack.Pop();
                Assign(node, node);
            }

        }
        public Stack<int> Reverse(Stack<int> input)
        {
            //Declare another stack to store the values from the passed stack
            Stack<int> temp = new Stack<int>();

            //While the passed stack isn't empty, pop elements from the passed stack onto the temp stack
            while (input.Count != 0)
                temp.Push(input.Pop());

            return temp;
        }

        public SimpleList<List<int>> cycles;

        /*public void FindAllCycles(int u, int d, bool[] isVisited, Stack<int> nodePath)
        {
            // Mark the current node  
            isVisited[u] = true;
            for (int i = 0; i < successors[u].Length; i++)
            {
                var nextNode = successors[u][i];
               if (nextNode == d)
               {
                   //nodePath.Push(nextNode);
                   //cycles.Add(nodePath.ToList());
                   //nodePath.Pop();
               }
               else if ((!isVisited[nextNode]))
               {
                   //nodePath.Push(nextNode);
                   FindAllCycles(nextNode, d, isVisited, nodePath);
                   //nodePath.Pop(); 
               }
               else if (nextNode < d)
                   break;
            }
            isVisited[u] = false;
        }*/


       /*  public void FindAllCycles(int startNode, int endNode, bool[] isVisited, SimpleList<int> nodePath)
         {
             // mark the current node  
             isVisited[startNode] = true;
             for (int i = 0; i < successors[startNode].Length; i++)
             {
                 var nextNode = successors[startNode][i];
                 if (nextNode == endNode)	// cycle found
                 {
                     nodePath.Append(nextNode);	// return cycle path
                     cycles = cycles.Append(nodePath);
                    numberOfCycles++;
                 }
                 else if ((!isVisited[nextNode] && nextNode > endNode))
                 {
                     FindAllCycles(nextNode, endNode, isVisited, nodePath.Append(nextNode));
                 }
             }
             //isVisited[startNode] = false;
         }*/
        int numberOfCycles = 0;
        public void FindAllCycles(int start)
        {
            var visited = new bool[this.cntStates+1];
            var stack = new Stack<Tuple<int, int>>();            
            int neighbor;
            stack.Push(new Tuple<int, int>(start, 0));
            while (stack.Count > 0)
            {
                var vertex = stack.Peek();
                var currentNode = vertex.Item1;
                var pointer = vertex.Item2;
                visited[currentNode] = true;
                if(successors[currentNode].Length <= pointer)
                {
                    stack.Pop();
                    visited[currentNode] = false;
                    continue;
                }
                do
                {
                    neighbor = successors[currentNode][pointer];
                    if (neighbor == start)    // cycle found
                    {
                        numberOfCycles += 1;                       
                        var pathArray = stack.ToList();
                        int size = stack.Count();
                        int[] itemList = new int[size+1];
                        itemList[size] = start;
                        pathArray.Reverse();
                        for (int k = 0; k < size; k++)
                            itemList[k] = pathArray[k].Item1; 
                        // Console.Write("\nPath: ");
                        //for (int l = 0; l < itemList.Length; l++)
                          //  Console.Write(itemList[l] + " ");
                        //Console.Write("\n-------------\n");
                        cycles = cycles.Append(itemList.ToList());
                    }
                    pointer++;
                } while (successors[currentNode].Length > pointer && (visited[neighbor] || neighbor < currentNode));

                if (successors[currentNode].Length <= pointer)
                {
                    stack.Pop();
                    visited[currentNode] = false;
                    continue;
                }
                var item = stack.Pop();
                stack.Push(Tuple.Create(item.Item1, pointer));
                stack.Push(Tuple.Create(neighbor, 0));                
            }

        }

        cop GetOps(CsUpdate[] updates, int x, int m)
        {
            cop operations = new cop(this.cntCount);
            for (int c = 0; c < this.cntCount; c++)
            {
                switch(updates[c])
                {
                    case CsUpdate.ADD0:
                        operations.Add(c, 0, 1);
                        break;
                    case CsUpdate.ADD1:
                        operations.Add(c, 0, 1);
                        break;
                    case CsUpdate.INCR:
                        operations.Add(c, 1, 1);
                        break;
                    case CsUpdate.INCR0:
                        operations.Add(c, 1, 1);
                        operations.Add(c, 0, 1);
                        break;
                    case CsUpdate.INCR1:
                        operations.Add(c, 1, 1);
                        operations.Add(c, 0, 1);
                        break;
                    case CsUpdate.INCR0_EXIT:
                        operations.Add(c, 0, 1);
                        operations.Add(c, 1, 1);
                        operations.Add(c, 2, 1);
                        break;
                    case CsUpdate.INCR1_EXIT:
                        operations.Add(c, 0, 1);
                        operations.Add(c, 1, 1);
                        operations.Add(c, 2, 1);
                        break;
                    case CsUpdate.EXIT:
                        operations.Add(c, 2, 1);
                        break;
                    case CsUpdate.NOOP:
                        if(this.usedCounters[x].Contains(c))
                            operations.Add(c, 2, 1);
                        break;
                }
            }
            return operations;
        }
        
     
       /* public void FindPath(int u, int d, bool[] isVisited, List<int> nodePath, double[] mapStateToCycles)
        {
            isVisited[u] = true;
           
            for (int i= 0; i < successors[u].Length; i++)
            {
                var nextNode = successors[u][i];
                if (nextNode.Equals(d))
                {
                    nodePath.Add(nextNode);
                    return;
                }
                else if (!isVisited[nextNode] && nextNode > d && mapStateToCycles[nextNode] == 0)
                {
                    nodePath.Add(nextNode);
                    FindPath(nextNode, d, isVisited, nodePath,
                                      mapStateToCycles);
                    nodePath.RemoveAt(nodePath.Count - 1);
                }
            }
            isVisited[u] = false;
        }*/
        
      
        public void InitConfAut()
        {
            this.mapConf = new Dictionary<conf, int>(new ConfEqualityComparer());
            this.mapConfStates = new Dictionary<int, conf>();
            this.confAut = new List<Tuple<int, int>>();
            confAut.Add(Tuple.Create<int, int>(0,0));
            countConf = 1;
        }

        long LongRandom(long min, long max, Random rand)
        {
            byte[] buf = new byte[8];
            rand.NextBytes(buf);
            long longRand = BitConverter.ToInt64(buf, 0);
            return (Math.Abs(longRand % (max - min)) + min);
        }

        internal class ItemComparer : IComparer<string>
        {
            int IComparer<string>.Compare(string x, string y)
            {
                return string.Compare(x, y);
            }
        }

        public void GenerateRandomText(int bound, bool verbose, string folder, string name, bool hybrid)
        {
            str = "";        // generated line
            visited = 0;        // number of visited nodes
            found = 1;          // number of discoverd nodes
            line = 1;           // number of lines
            var symbol = -1;        // generated symbol 
            int prefixSize = 0;     // prefix size
            unvisited = new SortedList<string, Object>(new ItemComparer());    // list of unvisited nodes
            var countUnvisited = 0;
            string prefix = "";     // prefix
            int cacheSize = 0;      // cache size
            distance = new double[200000000];
            pre = new int[200000000];
            sizeCA = new int[200000000];
            finalState = new bool[200000000];
            // set current configuration and state of configuration automata
            this.currentConf = ValueTuple.Create(1, this.cs);
            this.currentState = 0;
            // map conf to state and wise versa
            mapConf[new conf(1, this.cs, this.counters)] = 0;
            mapConfStates[0] = new conf(1, this.cs, this.counters);
            // distance from initial state and size of CA for initial state
            distance[0] = 0;
            pre[0] = 0;
            sizeCA[0] = SetWeightOfState(1, this.cs);
            finalState[0] = this.finalSet[0];
            #region output text 
            // create dot file with configuration automata
            if (verbose)
                dotFile = "digraph g{\nnode[shape=record fontname=Calibri fontsize = 20]\nedge[fontname = Calibri fontsize = 20]";
            #endregion
          // Console.WriteLine("Generating text.\n");
            // compute until you reach 'bound' visited states
            while (visited < bound)
            {
                #region remember size of cache
                if (verbose)
                { 
                    cacheSize = this.mapConf.Count();
                }
                #endregion
                // compute until reach final state
                int k = 0;
                while (((this.finalSet[this.currentConf.Item1] ? this.CheckFinalConditionWhileGen() : 1) != 0))
                {
                    // compute next generated symbol 
                    symbol = this.NextStep(verbose, hybrid);
                    
                    if (symbol == -1)   // no successors
                        break;
                    // choose symbol from minterm
                    str += this.inputAlgebra.ChooseUniformly(this.minSymbols[symbol]);
                    //Console.WriteLine(str);
                    // count symbols
                    k++;
                    
                    // more than bound
                /*    if ((visited + k) >= bound)
                    {
                        # region output text
                        if (verbose)
                        {
                            // compute visited states
                            int va = (str.Length - prefixSize + 1);
                            visited += va;   
                            // compute discovered states
                            int fa = this.mapConf.Count() - cacheSize;
                            found += fa;
                            // create output texxt
                            string output = "Line " + line + ":\t|Prefix| = " + prefixSize + ",\tVisited=" + va + "(" + visited + "),\tFound=" + fa + "(" + found + "),";
                            // no successor (all successors visited)
                            if (symbol == -1)
                                output += " !";
                            else
                            {
                                // final state
                                output += " F";
                            }
                            if (verbose) // write prefix and expanded text
                                output += "\n" + prefix + " | " + str.Substring(prefixSize, str.Length - prefixSize);
                            Console.WriteLine(output);
                        }
                        #endregion
                        // write string to file
                        File.AppendAllText(name, str + "\n");
                        Console.WriteLine("--------- Text generated.  -----------\n");
                        #region output text
                        if (verbose)
                        {
                            dotFile += "}";
                            using (var sw = new StreamWriter(folder + "/dotfile_" + LongRandom(100000, 100050, new Random()) + ".dot", true))
                            {
                                sw.WriteLine(dotFile);
                            }
                        }
                        #endregion
                        return;
                    }*/
                }
                # region output text 
                // compute visited states
                int v = (str.Length - prefixSize + 1); 
                visited += v;

               /*if (verbose)
                   {
                       // compute discovered states

                   Console.WriteLine(output);
                   int f = this.mapConf.Count() - cacheSize;
                       found += f;
                       // create output text
                       string output = "Line " + line + ":\t|Prefix| = " + prefixSize + ",\tVisited=" + v + "(" + visited + "),\tFound=" + f + "(" + found + "),";
                       // no successor (all successors visited)
                       if (symbol == -1)
                           output += " !";
                       else
                       {
                           // final state
                           output += " F";
                       }
                       if (verbose) // write prefix and expanded text
                           output += "\n" + prefix + " | " + str.Substring(prefixSize, str.Length - prefixSize);
                       Console.WriteLine(output);
                   }*/
                /*  if(symbol != -1)
                  {
                      str = str.Remove(str.Length-1);
                  }*/
                File.AppendAllText(name, str + "\n");
                str = "";
                // no unvisited states
                if (unvisited.Count == 0)
                {
                   /* Console.WriteLine("--------- State space explored.  -----------\n");
                    if (verbose)
                    {
                        dotFile += "}";
                        using (var sw = new StreamWriter(folder + "/dotfile_" + LongRandom(100000, 100050, new Random()) + ".dot", true))
                        {
                            sw.WriteLine(dotFile);
                        }
                    }*/
                    return;
                }
                #endregion
                // select unvisited state according to size of CAs and shortest path to initial state
                int c = (int)unvisited.Values[0];
                unvisited.RemoveAt(0);
                countUnvisited -= 1;
                var confSet = mapConfStates[c];
                this.currentConf = confSet.RecoverCS(c);
                this.currentState = c;
                 // get prefix
                 prefix = this.GetPrefix(c);
                 str += prefix;
                
                #region output text
                if (verbose)
                {
                    prefixSize = prefix.Length;
                    line += 1;
                }             
                #endregion
            }
            # region outputext
         /*   if (verbose)
            {
                dotFile += "}";
                using (var sw = new StreamWriter(folder + "/dotfile_" + LongRandom(100000, 100050, new Random()) + ".dot", true))
                {
                    sw.WriteLine(dotFile);
                }
            }*/
            #endregion  
            Console.WriteLine("--------- Text generated. -----------\n");
            return;
        }

      
        private string GetPrefix(int node)
        {
             // state in configuration automata
            var pre = this.confAut[node];
            if (pre.Item1 == 0)
                return this.inputAlgebra.ChooseUniformly(this.minSymbols[pre.Item2]).ToString();
            return GetPrefix(pre.Item1) + this.inputAlgebra.ChooseUniformly(this.minSymbols[pre.Item2]);
        }

        private List<Tuple<CsUpdate[], int, int>> GetMovesFromState(int state)
        {
            countSucc = 0;
            List<Tuple<CsUpdate[], int, int>> succs = new List<Tuple<CsUpdate[], int, int>>();
            for (int m = 0; m < minterms.Length; m++)
            {
                // go staightward to the next state
                if (this.transitionTable[state][m] > 0)
                {
                    var t = Tuple.Create<CsUpdate[], int, int>(null, this.transitionTable[state][m], m);
                    succs.Add(t);
                    countSucc += 1;
                }
                else if (this.transitionTable[state][m] < 0)
                {
                    int index = 0;
                    var ac = this.usedCounters[this.currentConf.Item1];
                    for (int c = 0; c < ac.Length; c++)
                    {
                        index |=  this.currentConf.Item2[ac[c]].flag << c * 2;
                    }
                    Tuple<CsUpdate[], int> chosenTran = null;
                    chosenTran = this.transInfoTable[-this.transitionTable[state][m]][index];
                       
                    if (chosenTran == null)
                        continue;
                    succs.Add(Tuple.Create<CsUpdate[], int, int>(chosenTran.Item1, chosenTran.Item2, m));
                    countSucc += 1;
                }
            }
            return succs;
        }

        private Tuple<CsUpdate[], int, double> GetMoveFromTo(int state, int nextState)
        {
           // List<Tuple<CsUpdate[], int, double>>  successors = new List<Tuple<CsUpdate[], int, double>>();
            Tuple < CsUpdate[], int, double> successor = null;
           
            for (int m = 0; m < minterms.Length; m++)
            {
                // go staightward to the next state
                if (this.transitionTable[state][m] == nextState)
                {
                    if(successor == null)
                       successor = Tuple.Create<CsUpdate[], int, double>(null, m, 0);
                    return successor;
                }
                else if (this.transitionTable[state][m] < 0)
                {
               //    if(cntCount < 7)
                 //   {
                        var info = this.transInfoTable[-this.transitionTable[state][m]];
                        for (int j = 0; j < info.Length; j++)
                        {
                            if (info[j] != null)
                            {
                                if (info[j].Item2 == nextState)
                                {
                                    successor = Tuple.Create<CsUpdate[], int, double>(info[j].Item1, m, 0);
                                    return successor;
                                }
                            }
                        }
                        continue;
                        /*  }
                          else
                          {
                              var info = this.tInfoTable[-this.transitionTable[state][m]];
                              foreach (int j in info.Keys)
                              {
                                  if (info[j] != null)
                                  {
                                      if (info[j].Item2 == nextState)
                                      {
                                          return Tuple.Create<CsUpdate[], int, double>(info[j].Item1, m, 0);
                                      }
                                  }
                              }
                              continue;
                          }*/

                    }
                }
            return successor;
        }

        int[][] GetOperations(CsUpdate[] updates, int x, int m)
        {
            int[][] operations = new int[this.cntCount][];
            for (int i = 0; i < this.cntCount; i++)
            {
                operations[i] = new int[] { 0, 0, 0 };
            }
            for (int c = 0; c < this.cntCount; c++)
            {
                switch (updates[c])
                {
                    case CsUpdate.ADD0:
                        operations[c][0] += 1;
                        break;
                    case CsUpdate.ADD1:
                        operations[c][0] += 1;
                        break;
                    case CsUpdate.INCR:
                        operations[c][1] += 1;
                        break;
                    case CsUpdate.INCR0:
                        operations[c][1] += 1;
                        operations[c][0] += 1;
                        break;
                    case CsUpdate.INCR1:
                        operations[c][1] += 1;
                        operations[c][0] += 1;
                        break;
                    case CsUpdate.INCR0_EXIT:
                        operations[c][0] += 1;
                        operations[c][1] += 1;
                        operations[c][2] += 1;
                        break;
                    case CsUpdate.INCR1_EXIT:
                        operations[c][0] += 1;
                        operations[c][1] += 1;
                        operations[c][2] += 1;
                        break;
                    case CsUpdate.EXIT:
                        operations[c][2] += 1;
                        break;
                    case CsUpdate.NOOP:
                        if (this.usedCounters[x].Contains(c))
                            operations[c][2] += 1;  // EXIT
                        break;
                }
            }
            return operations;
        }

      /*  public static void Shuffle(List<Tuple<double,int>> ts)
        {
            var count = ts.Count;
            var last = count - 1;
            Random ri = new Random();
            for (var i = 0; i < last; ++i)
            {
                int r = ri.Next(i, count);
                var tmp = ts[i];
                ts[i] = ts[r];
                ts[r] = tmp;
            }
        }*/

       /* private int NextReverseStep(int state, List<Tuple<double, int>>[] nextTable, double randomShuffle = 4)
        {
            for (int ns = nextTable[state].Count-1; ns >= 0 ; ns--)
            {
                var nextState = nextTable[state][ns].Item2;
                Tuple<CsUpdate[], int, double> successor = this.GetMoveFromTo(state, nextState);
                if (successor == null)
                    continue;
                return successor.Item2;
            }
            return Int16.MaxValue;
        }*/

        string ToString(ValueTuple<int, BasicCountingSet[]> cc, double dist, double size, double w)
        {
            string s = cc.Item1 + " | ";
            for (int i = 0; i < cc.Item2.Length; i++)
            {
                s += cc.Item2[i].ToString();
            } 
            s += " | Dist: " + dist + " | Size: " + size + " | Weight: " + w;
            return s;
        }

        ValueTuple<int, BasicCountingSet[]> copyIt(int state, BasicCountingSet[] cs)
        {
            BasicCountingSet[] copyCS= null;
            if (counters.Length != 0)
            {
                copyCS = new BasicCountingSet[cs.Length];

                for (int i = 0; i < cs.Length; i++)
                {
                    copyCS[i] = new BasicCountingSet(counters[i]);
                    copyCS[i] = cs[i].CopyIt(copyCS[i]);

                }
            }
            return ValueTuple.Create(state, copyCS);
        }

        private string ConfToString(ValueTuple<int, BasicCountingSet[]> cc)
        {
            string s = cc.Item1 + " | ";
            for (int i = 0; i < cc.Item2.Length; i++)
            {
                s += cc.Item2[i].ToString();
            }
            return s;
        }

        private int NextStep(bool verbose,  bool hybrid)
        {            
            bool newEdge = false;
            // get successors (update, target state, minterm)        
            List<Tuple<CsUpdate[], int, int>> successors = this.GetMovesFromState(this.currentConf.Item1);
            // no successors
            if (successors == null)
                  return -1;

            // best next configuration (successor)
            ValueTuple<int, BasicCountingSet[]> best = new ValueTuple<int, BasicCountingSet[]>();
            int bestState = -1;
            int minterm = -1;
            string output = "";
            // iterate over successors
            for (var s = 0; s < countSucc; s++)
            {
                #region update target registers and construct set of valid counting sets
                var successor = successors[s];
                output = "";
                // var conf = new conf(successor.Item2, this.currentnextConf.Item2, this.counters);
                var nextConf = copyIt(successor.Item2, this.currentConf.Item2);

                // iterate over updated counters
                if (this.updatedCounters[currentConf.Item1][successor.Item3] != null)
                {
                    foreach (var i in this.updatedCounters[currentConf.Item1][successor.Item3])
                    {
                        if(verbose)
                         output += successor.Item1[i].ToString() + "(c" + i + "); ";
                        switch (successor.Item1[i])
                        {
                            case CsUpdate.INCR1:
                                nextConf.Item2[i].IncrPush1();
                                break;
                            case CsUpdate.INCR1_EXIT:
                                nextConf.Item2[i].IncrPush1();
                                break;
                            case CsUpdate.INCR:
                                nextConf.Item2[i].Incr();
                                break;
                            case CsUpdate.COPY:
                                break;
                            case CsUpdate.ADD0:
                                nextConf.Item2[i].Set0();
                                break;
                            case CsUpdate.ADD1:
                                nextConf.Item2[i].Set1();
                                break;
                            case CsUpdate.INCR0:
                                nextConf.Item2[i].IncrPush0();
                                break;
                            case CsUpdate.INCR01:
                                nextConf.Item2[i].IncrPush1();
                                nextConf.Item2[i].Push0();
                                break;
                            case CsUpdate.INCR_EXIT:
                                nextConf.Item2[i].Incr();
                                break;
                            case CsUpdate.INCR0_EXIT:
                                nextConf.Item2[i].IncrPush0();
                                break;
                            case CsUpdate.INCR01_EXIT:
                                nextConf.Item2[i].IncrPush1();
                                nextConf.Item2[i].Push0();
                                break;
                            case CsUpdate.ADD1_EXIT:
                                nextConf.Item2[i].Set1();
                                break;
                            case CsUpdate.ADD0_EXIT:
                                nextConf.Item2[i].Set0();
                                break;
                            case CsUpdate.ADD01:
                                nextConf.Item2[i].Set1();
                                nextConf.Item2[i].Push0();
                                break;
                            case CsUpdate.COPY_ADD0:
                                nextConf.Item2[i].Push0();
                                break;
                            case CsUpdate.COPY_ADD1:
                                nextConf.Item2[i].Push1();
                                break;
                            case CsUpdate.COPY_ADD01:
                                nextConf.Item2[i].Push1();
                                nextConf.Item2[i].Push0();
                                break;
                            default:
                                nextConf.Item2[i].Clear();
                                break;
                        }
                        // recalculate flag for CS
                        var max = nextConf.Item2[i].Max();

                        if (max >= counters[i].LowerBound)
                        {
                            if (max >= counters[i].UpperBound && nextConf.Item2[i].IsSingleton())
                                nextConf.Item2[i].flag = (int)CsCondition.CANLOOP; // CANLOOP instead of HIGH!!
                            else
                                nextConf.Item2[i].flag = (int)CsCondition.MIDDLE;
                        }
                        else
                        {
                            nextConf.Item2[i].flag = (int)CsCondition.LOW;
                        }
                    }
                }
                
                // reset CS if exiting counting state
                if (this.usefulCounters[currentConf.Item1][successor.Item3] != null)
                {
                    foreach (var i in this.usefulCounters[currentConf.Item1][successor.Item3])
                    {
                        nextConf.Item2[i].Clear();
                        var max = nextConf.Item2[i].Max();
                        if (max >= counters[i].LowerBound)
                        {
                            if (max >= counters[i].UpperBound && nextConf.Item2[i].IsSingleton())
                                nextConf.Item2[i].flag = (int)CsCondition.CANLOOP; // CANLOOP instead of HIGH!!
                            else
                                nextConf.Item2[i].flag = (int)CsCondition.MIDDLE;
                        }
                        else
                        {
                            nextConf.Item2[i].flag = (int)CsCondition.LOW;
                        }
                    }
                }              
                #endregion

                if((this.finalSet[nextConf.Item1] ? this.CheckFinalConditionWhileGen(nextConf) : 1) == 0)
                {   // final state
                    continue; // skip state
                }
                

                #region select best successor
                
                // create representation of configuration
                conf mapNextConf;
                mapNextConf = new conf(nextConf.Item1, nextConf.Item2, this.counters);
                 // configuration not in the case
                bool flagS = mapConf.ContainsKey(mapNextConf);
                
                if (!flagS)
                {
                    int nextState = countConf;
                    // distance
                    distance[nextState] = distance[currentState] + 1;
                    pre[nextState] = currentState;
                    // size of CA
                    sizeCA[nextState] = SetWeightOfState(nextConf.Item1, nextConf.Item2);
                    // final state
                    finalState[nextState] = this.finalSet[nextConf.Item1];
                  //  #region output text
                    // creat dot file
                  /*  if (verbose)
                    {
                        var m = this.inputAlgebra.ChooseUniformly(this.minSymbols[successor.Item3]);
                        dotFile += "\n" + currentState + "->" + nextState + "[label=\" " + m + " | " + output+ "\"]";
                        if (hybrid)
                        {
                            dotFile += "\n" + currentState + "[label=\"" + this.ToString(currentConf, distance[currentState], sizeCA[currentState], this.mapStateToCycles[currentConf.Item1]) + "\"]";
                            dotFile += "\n" + nextState + "[label=\"" + this.ToString(nextConf, distance[nextState], sizeCA[nextState], this.mapStateToCycles[nextConf.Item1]) + "\"]";
                        }
                        else
                        {
                            dotFile += "\n" + currentState + "[label=\"" + this.ToString(currentConf,distance[currentState], sizeCA[currentState], 0) + "\"]";
                            dotFile += "\n" + nextState + "[label=\"" + this.ToString(nextConf, distance[nextState], sizeCA[nextState], 0) + "\"]";
                        }

                        if ((this.finalSet[nextConf.Item1] ? this.CheckFinalConditionWhileGen(mapNextConf) : 1) == 0)
                        {
                            dotFile += "\n" + nextState + "[fillcolor = lightgrey, style=filled]";
                        }
                    }*/
                    #endregion

                   // map conf to state and vice versa
                    mapConf[mapNextConf] = nextState;
                    mapConfStates[nextState] = mapNextConf;
                    // add configuration to automata with a pointer to predecessor
                    confAut.Add(Tuple.Create<int, int>(currentState, successor.Item3));
                    countConf += 1;
                    // no successor visited yet
                    if (best.Item1 == 0)
                    {
                        // remember minterm and configuration
                        minterm = successor.Item3;                        
                        best = copyIt(nextConf.Item1, nextConf.Item2);
                        bestState = nextState;
                    }
                    else
                    {
                        // compare with the best configuration so far
                        bool flag;
                        if (hybrid)
                        {
                            flag = !Better(bestState, nextState, this.mapStateToCycles[best.Item1], this.mapStateToCycles[nextConf.Item1]);
                        }
                        else
                            flag = !Better(bestState, nextState, 0, 0);
                        if (flag)
                        {
                            //var mapBestConf = new conf(best.Item1, best.Item2, this.counters);
                            //bestState = mapConf[mapBestConf];
                            
                            // add previous configuration to unvisited
                            unvisited.Add(this.GetKey(bestState), bestState);
                            countUnvisited += 1;
                            // update best configuration and minterm
                            best = copyIt(nextConf.Item1, nextConf.Item2);
                            bestState = nextState;
                            minterm = successor.Item3;
                            newEdge = false;
                        }
                        else
                        {
                            // add configuration to unvisited
                            unvisited.Add(this.GetKey(nextState), nextState);
                            countUnvisited += 1;
                        }
                    }
                }
                else
                {
                    // if conf already in cash, get the state of conf
                    int nextState = mapConf[mapNextConf];
                    if(distance[nextState] > distance[currentState] +1)
                    {
                        pre[nextState] = currentState;
                        distance[nextState] = distance[currentState] + 1;
                    }
                    // if configuration not visited
                    if (unvisited.Values.Contains(nextState))
                    {
                        // if no successor not yet visited
                        if (best.Item1 == 0)
                        {
                            // remember minterm and successor
                            minterm = successor.Item3;
                            best = copyIt(nextConf.Item1, nextConf.Item2);
                            bestState = nextState;
                            // remove state from unvisited
                            var index = unvisited.IndexOfValue(nextState);
                            unvisited.RemoveAt(index);
                            countUnvisited -= 1;
                            newEdge = true;
                        }
                        else
                        {  
                            //TODO: chyba
                            bool flag;
                            if (hybrid)
                            {
                                flag = !Better(bestState, nextState, this.mapStateToCycles[best.Item1], this.mapStateToCycles[nextConf.Item1]);
                            }
                            else
                                flag = !Better(bestState, nextState, 0, 0);
                            if (flag)
                            {
                                unvisited.Add(this.GetKey(bestState), bestState);
                                countUnvisited += 1;
                                //var mapBestConf = new conf(best.Item1, best.Item2, this.counters);
                                //bestState = mapConf[mapBestConf];
                                best = copyIt(nextConf.Item1, nextConf.Item2);
                                bestState = nextState;
                                minterm = successor.Item3;
                                newEdge = true;
                            }
                        }
                    }
                }
                //#endregion
            }

            if (best.Item1 != 0)
            {
                /*if(newEdge && verbose)
                {
                    #region create output chart
                    var mapBestConf = new conf(best.Item1, best.Item2, this.counters);
                    var m = this.inputAlgebra.ChooseUniformly(this.minSymbols[minterm]);
                    dotFile += "\n" + currentState + "->" + bestState + "[label=\" " + m + " | " + output + "\"]";
                    
                    if (hybrid)
                    {
                        dotFile += "\n" + currentState + "[label=\"" + this.ToString(currentConf, distance[currentState], sizeCA[currentState], this.mapStateToCycles[currentConf.Item1]) + "\"]";
                        dotFile += "\n" + bestState + "[label=\"" + this.ToString(best, distance[bestState], sizeCA[bestState], this.mapStateToCycles[best.Item1]) + "\"]";
                    }
                    else
                    {
                        dotFile += "\n" + currentState + "[label=\"" + this.ToString(currentConf, distance[currentState], sizeCA[currentState], 0) + "\"]";
                        dotFile += "\n" + bestState + "[label=\"" + this.ToString(best, distance[bestState], sizeCA[bestState], 0) + "\"]";
                    }
                    if ((this.finalSet[best.Item1] ? this.CheckFinalConditionWhileGen(mapBestConf) : 1) == 0)
                    {
                        dotFile += "\n" + bestState + "[fillcolor = lightgrey, style=filled]";
                    }
                    #endregion
                }*/
                // copy to current conf the best one
                this.currentConf = copyIt(best.Item1, best.Item2);
                this.currentState = bestState;
            }
            return minterm;
        }

        public string GetKey(int state)
        {
            int index = 0;
            string k = (finalState[state] ? "a-" : "b-") + distance[state].ToString() + "-" + sizeCA[state].ToString() + "-";
            string key = "";
            do
            {
                key = k + index.ToString();
                index++;
            } while (this.unvisited.ContainsKey(key));
            return key;           
        }

      
        public double ComputeWeight(int[] path)
        {
            double w = 0;
            
            for (int i = 0; i < path.Length-1; i++)
            {
                int x = path[i];
                int y = path[i+1];
                cop ops = this.deltaPre[x][y];  // get counter operation for the edge
                //var a = 0;
                for (int c = 0; c < this.cntCount; c++)
                {
                    if (ops.Get(c, 2) != 0)
                        return 0;
                    else
                    {
                        var v = (ops.Get(c, 1) != 0)?(this.counters[c].UpperBound / ops.Get(c, 1)):this.counters[c].UpperBound;
                        var add = ops.Get(c, 0);
                        w += (v * add);
                    }
                }
            }           
            return w;
        }

        /// <summary>
        /// Compute the target state for source state q and input character c.
        /// All uses of Delta must be inlined for efficiency. 
        /// This is the purpose of the MethodImpl(MethodImplOptions.AggressiveInlining) attribute.
        /// </summary>
        /// <param name="c">input character</param>
        /// <param name="q">state id of source regex</param>
        /// <param name="regex">target regex</param>
        /// <returns>state id of target regex</returns>
        public int Delta(int symbol)
        {
            // choose a transition or find target state
            var target = this.transitionTable[currentState][symbol];
            if (target > 0)   // target state
            {
                currentState = target;
                // check if the current state is final
                return (this.finalSet[target] ? 0 : 1);
            }
            else if (target < 0)    // key to transition table
            {
                // count index to transition table
                 int index = 0;
                 var ac = this.usedCounters[currentState];
                 for (int c = 0; c < ac.Length; c++)
                 {
                     int i = ac[c];
                     index = index | cs[i].flag << i * 4;
                 }
                var chosenTran = this.transInfoTable[-target][index];
                if (chosenTran.Item2 == 0)
                    return -1;
               for (var a = 0; a < this.updatedCounters[currentState][symbol].Length; a++)
                {
                    #region update target registers and construct set of valid counting sets
                    int i = this.updatedCounters[currentState][symbol][a];
                    switch (chosenTran.Item1[i])
                    {
                        case CsUpdate.INCR1:
                            cs[i].IncrPush1();
                            break;
                        case CsUpdate.INCR1_EXIT:
                            cs[i].IncrPush1(); // the same as INCR01
                            break;
                        case CsUpdate.INCR:
                            cs[i].Incr();
                            break;
                        case CsUpdate.ADD0:
                            cs[i].Set0();
                            break;
                        case CsUpdate.ADD1:
                            cs[i].Set1();
                            break;
                        case CsUpdate.INCR0:
                            cs[i].IncrPush0();
                            break;
                        case CsUpdate.INCR01:
                            cs[i].IncrPush01();
                            break;
                        case CsUpdate.INCR_EXIT:
                            cs[i].Incr();
                            break;
                        case CsUpdate.INCR0_EXIT:
                            cs[i].IncrPush0(); // the same as INCR0
                            break;
                        case CsUpdate.INCR01_EXIT:
                            cs[i].IncrPush01(); // the same as INCR01
                            break;
                        case CsUpdate.ADD1_EXIT:
                            cs[i].Set1();
                            break;
                        case CsUpdate.ADD0_EXIT:
                            cs[i].Set0();
                            break;
                        case CsUpdate.ADD01:
                            cs[i].Set1();
                            cs[i].Push0();
                            break;
                        case CsUpdate.COPY_ADD0:
                            cs[i].Push0();
                            break;
                        case CsUpdate.COPY_ADD1:
                            cs[i].Push1();
                            break;
                        case CsUpdate.COPY_ADD01:
                            cs[i].Push1();
                            cs[i].Push0();
                            break;
                        default:
                            cs[i].Clear();
                            break;
                    }
                    
                        var max = cs[i].Max();
                        if (max >= counters[i].LowerBound)
                        {
                            if (max >= counters[i].UpperBound && cs[i].IsSingleton())
                                cs[i].flag = (int)CsCondition.HIGH;
                            else
                                cs[i].flag = (int)CsCondition.MIDDLE;
                        }
                        else
                        {
                            cs[i].flag = (int)CsCondition.LOW;
                        }
                    
                    #endregion
                }
                currentState = chosenTran.Item2;
                if (cs == null) // counter is above maximum
                    return -1;
                // check final condition
                return (this.finalSet[currentState] ? this.CheckFinalCondition() : 1);
            }
            // otherwise is a sink state
            else
            {
                return -1;
            }
        }
        
        

        private int MaximumWeight(bool[] shortestPathTreeSet, int verticesCount)
        {
            double max = double.MinValue;
            int maxIndex = 0;

            for (int v = 1; v < verticesCount; ++v)
            {
                // skip final state 
                if (!this.finalSet[v] && shortestPathTreeSet[v] == false && this.mapStateToCycles[v] >= max)
                {
                    max = mapStateToCycles[v];
                    maxIndex = v;
                }
            }

            return maxIndex;
        }

        private void Print(int verticesCount)
        {
            Console.WriteLine("Vertex    Distance from source   Pre vertex");
            for (int i = 1; i < verticesCount+1; ++i)
                Console.WriteLine("{0}\t  {1}\t\t\t  {2}", i, distance[i], pre[i]);
        }

       

    }

    /// <summary>
    /// Counting-set Automaton
    /// </summary>
    public class CsAutomaton<S> : Automaton<CsLabel<S>>
    {
        PowerSetStateBuilder stateBuilder;
        Dictionary<int, ICounter> countingStates;
        HashSet<int> origFinalStates;

        CsAlgebra<S> productAlgebra;

        /// <summary>
        /// Underlying Cartesian product algebra
        /// </summary>
        public CsAlgebra<S> ProductAlgebra
        {
            get
            {
                return productAlgebra;
            }
        }

        Dictionary<int, HashSet<int>> activeCounterMap;

        HashSet<int> finalCounterSet;


        ICounter[] counters;

        public CsAutomaton(CsAlgebra<S> productAlgebra, Automaton<CsLabel<S>> aut, PowerSetStateBuilder stateBuilder, Dictionary<int, ICounter> countingStates, HashSet<int> origFinalStates) : base(aut)
        {
            this.stateBuilder = stateBuilder;
            this.countingStates = countingStates;
            this.origFinalStates = origFinalStates;
            activeCounterMap = new Dictionary<int, HashSet<int>>();
            finalCounterSet = new HashSet<int>();
            counters = new ICounter[countingStates.Count];
            foreach (var q in aut.States)
            {
                var q_set = new HashSet<int>();
                activeCounterMap[q] = q_set;
                foreach (var mem in stateBuilder.GetMembers(q))
                {
                    if (countingStates.ContainsKey(mem))
                    {
                        var counterId = countingStates[mem].CounterId;
                        q_set.Add(counterId);
                        if (origFinalStates.Contains(mem))
                            finalCounterSet.Add(counterId);
                        counters[counterId] = countingStates[mem];
                    }
                }
            }
            this.productAlgebra = productAlgebra;
            stateDescr[InitialState] = SpecialCharacters.S(0);
        }

        int GetOriginalInitialState()
        {
            foreach (var q0 in stateBuilder.GetMembers(InitialState))
                return q0;
            throw new AutomataException(AutomataExceptionKind.SetIsEmpty);
        }

        bool __hidePowersets = false;
        internal bool __debugmode = false;

        public void ShowGraph(string name = "CsAutomaton", bool debumode = false, bool hidePowersets = false)
        {
            __hidePowersets = hidePowersets;
            __debugmode = debumode;
            base.ShowGraph(name);
        }

        public void SaveGraph(string name = "CsAutomaton", bool debumode = false, bool hidePowersets = false)
        {
            __hidePowersets = hidePowersets;
            __debugmode = debumode;
            base.SaveGraph(name);
        }


        Dictionary<int, string> stateDescr = new Dictionary<int, string>();

        /// <summary>
        /// Describe the state information, including original states if determinized, as well as counters.
        /// </summary>
        public override string DescribeState(int state)
        {
            string s;
            if (!stateDescr.TryGetValue(state, out s))
            {
                s = SpecialCharacters.S(stateDescr.Count);
                stateDescr[state] = s;
            }

            var mems = new List<int>(stateBuilder.GetMembers(state));
            mems.Sort();
            if (!__hidePowersets)
            {
                s += "\n" + "{";
                foreach (var q in mems)
                {
                    if (!s.EndsWith("{"))
                        s += ",";
                    s += SpecialCharacters.q(q);
                }
                s += "}";
            }
            var state_counters = GetCountersOfState(state);
            var state_counters_list = new List<int>(state_counters);
            state_counters_list.Sort();
            foreach (var c in state_counters_list)
            {
                s += "\n";
                s += "(" + SpecialCharacters.c(c) + ")";
                //s += "(" + counters[c].LowerBound + 
                //    SpecialCharacters.LEQ + SpecialCharacters.c(c) + SpecialCharacters.LEQ + counters[c].UpperBound + ")";
                if (finalCounterSet.Contains(c))
                {
                    s += SpecialCharacters.XI_LOWERCASE + SpecialCharacters.ToSubscript(c);
                    s += SpecialCharacters.CHECKMARK;
                }
            }

            return s;
        }

        /// <summary>
        /// Describe if the initial state is associuated with a counter, if so then set it to {0}
        /// </summary>
        public override string DescribeStartLabel()
        {
            var initcounters = activeCounterMap[InitialState].GetEnumerator();
            if (initcounters.MoveNext())
            {
                var c = initcounters.Current;
                return string.Format("{0}={{0}}", SpecialCharacters.c(c));
            }
            else
                return "";
        }

        public override string DescribeLabel(CsLabel<S> lab)
        {
            return lab.ToString(__debugmode);
        }

        /* public static CsAutomaton<S> CreateFrom(CountingAutomaton<S> ca)
         {
             var productmoves = new List<Move<CsPred<S>>>();
             var counters = ca.counters;
             var alg = new CsAlgebra<S>(((CABA<S>)ca.Algebra).builder.solver, counters);
             foreach (var move in ca.GetMoves())
             {
                 var ccond = alg.TrueCsConditionSeq;
                 if (ca.IsCountingState(move.SourceState))
                 {
                     var counter = ca.GetCounter(move.SourceState);
                     var cid = counter.CounterId;
                     if (move.Label.Item2.First.OperationKind == CounterOp.EXIT ||
                         move.Label.Item2.First.OperationKind == CounterOp.EXIT_SET0 ||
                         move.Label.Item2.First.OperationKind == CounterOp.EXIT_SET1)
                     {
                         if (counter.LowerBound == counter.UpperBound && !ca.HasMovesTo(move.SourceState, move.Label.Item1.Element))
                             ccond = ccond.And(cid, CsCondition.HIGH);
                         else if (counter.LowerBound > 0)
                             ccond = ccond.And(cid, CsCondition.CANEXIT);
                         else
                             ccond.And(cid, CsCondition.NONEMPTY);
                     }
                     else
                     {
                         if (move.Label.Item2.First.OperationKind != CounterOp.INCR)
                             throw new AutomataException(AutomataExceptionKind.InternalError);

                         if (counter.LowerBound == counter.UpperBound && !ca.HasMovesTo(move.SourceState, move.Label.Item1.Element))
                             ccond = ccond.And(cid, CsCondition.LOW);
                         else
                             ccond = ccond.And(cid, CsCondition.CANLOOP);
                     }
                 }
                 if (ccond.IsSatisfiable)
                 {
                     var pmove = Move<CsPred<S>>.Create(move.SourceState, move.TargetState, alg.MkPredicate(move.Label.Item1.Element, ccond));
                     productmoves.Add(pmove);
                 }
             }
             var prodaut = Automaton<CsPred<S>>.Create(alg, ca.InitialState, ca.GetFinalStates(), productmoves);

             PowerSetStateBuilder sb;
             var det = prodaut.Determinize(out sb);

             //add predicate that all counters associated with the state are nonempty
             var counterFilter = new Dictionary<int, CsConditionSeq>();
             foreach (var state in det.GetStates())
             {
                 var stateCounterFilter = alg.TrueCsConditionSeq;
                 foreach (var q in sb.GetMembers(state))
                     if (ca.IsCountingState(q))
                         stateCounterFilter = stateCounterFilter.And(ca.GetCounter(q).CounterId, CsCondition.NONEMPTY);
                 counterFilter[state] = stateCounterFilter;
             }

             var csmoves = new List<Move<CsLabel<S>>>();

             //make disjunction of the guards of transitions with same update sequence
             var trans = new Dictionary<Tuple<int,int>,Dictionary<CsUpdateSeq, CsPred<S>>>();

             foreach (var dmove in det.GetMoves())
             { 
                 foreach (var prodcond in dmove.Label.GetSumOfProducts())
                 {
                     var upd = CsUpdateSeq.MkNOOP(ca.NrOfCounters);
                     foreach (var q in sb.GetMembers(dmove.SourceState))
                         upd = upd | ca.GetCounterUpdate(q, prodcond.Item2, prodcond.Item1);
                     //make sure all counter guards are nonempty
                     //determinization may create EMPTY counter conditions that are unreachable
                     //while all counters associated with a state are always nonempty
                     var counterGuard = prodcond.Item1 & counterFilter[dmove.SourceState];
                     if (counterGuard.IsSatisfiable)
                     {
#region replace set with incr if possible
                         for (int i = 0; i < upd.Length; i++)
                         {
                             var guard_i = counterGuard[i];
                             if (guard_i == CsCondition.HIGH)
                             {
                                 var upd_i = upd[i];
                                 switch (upd_i)
                                 {
                                     case CsUpdate.ADD0:
                                         upd = upd.Set(i, CsUpdate.INCR0);
                                         break;
                                     case CsUpdate.ADD1:
                                         upd = upd.Set(i, CsUpdate.INCR1);
                                         break;
                                     case CsUpdate.ADD01:
                                         upd = upd.Set(i, CsUpdate.INCR01);
                                         break;
                                     default:
                                         break;
                                 }
                             }
                         }
#endregion

                         var guard = alg.MkPredicate(prodcond.Item2, counterGuard);
                         var statepair = new Tuple<int, int>(dmove.SourceState, dmove.TargetState);
                         Dictionary<CsUpdateSeq, CsPred<S>> labels;
                         if (!trans.TryGetValue(statepair, out labels))
                         {
                             labels = new Dictionary<CsUpdateSeq, CsPred<S>>();
                             trans[statepair] = labels;
                         }
                         CsPred<S> pred;
                         if (!labels.TryGetValue(upd, out pred))
                             pred = guard;
                         else
                             pred = guard | pred;
                         labels[upd] = pred;
                     }
                     else
                     {
                         ;
                     }
                 }
             }

             Func<S,string> pp = ((CABA<S>)ca.Algebra).builder.solver.PrettyPrint;
             foreach (var entry in trans)
             {
                 var s = entry.Key.Item1;
                 var t = entry.Key.Item2;
                 foreach (var label in entry.Value)
                 {
                     var upd = label.Key;
                     var psi = label.Value;
                     csmoves.Add(Move<CsLabel<S>>.Create(s, t, CsLabel<S>.MkTransitionLabel(psi, upd, pp)));
                 }
             }

             var csa_aut = Automaton<CsLabel<S>>.Create(null, det.InitialState, det.GetFinalStates(), csmoves, true, true);

             var fs = new HashSet<int>(ca.GetFinalStates());

             var csa = new CsAutomaton<S>(alg, csa_aut, sb, ca.countingStates, fs);

             return csa;
         }*/

        /// <summary>
        /// Get the active counters associated with the given state.
        /// The set is empty if this state is not asscociated with any counters.
        /// </summary>
        public HashSet<int> GetCountersOfState(int state)
        {
            return activeCounterMap[state];
        }

        /// <summary>
        /// Get the total number of counters
        /// </summary>
        public int NrOfCounters
        {
            get
            {
                return counters.Length;
            }
        }

        /// <summary>
        /// Get the counter info associated with the given counter id
        /// </summary>
        /// <param name="counterId">must be a number between 0 and NrOfCounters-1</param>
        /// <returns></returns>
        public ICounter GetCounterInfo(int counterId)
        {
            return counters[counterId];
        }

        /// <summary>
        /// Returns true if the given counter is a final counter, thus, in final state 
        /// contributes to the overall final state condition.
        /// </summary>
        /// <param name="counterId">must be a number between 0 and NrOfCounters-1</param>
        /// <returns></returns>
        public bool IsFinalCounter(int counterId)
        {
            return finalCounterSet.Contains(counterId);
        }
    }

    public class CsLabel<S>
    {
        bool isFinalCondition;
        //public readonly CsPred<S> G;
        public bool Noop;
        public readonly CsAlgebra<S> LeafAlg;
        public readonly CsPred<S> Guard;
        public readonly CsConditionSeq CGuard;
        public CsUpdateSeq Updates;
        Func<S, string> InputToString;
        public int weight = -Int16.MaxValue;


        public bool IsFinalCondition
        {
            get { return isFinalCondition; }
        }

    
        CsLabel(bool isFinalCondition, CsPred<S> guard, CsConditionSeq cGuard, CsAlgebra<S> alg, CsUpdateSeq updates, Func<S, string> inputToString)
        {
            this.isFinalCondition = isFinalCondition;
            this.Guard = guard;
            this.CGuard = cGuard;
            this.Updates = updates;
            this.InputToString = inputToString;
            this.Noop = false;
            this.LeafAlg = alg;
        }
        

        public static CsLabel<S> MkFinalCondition(CsPred<S> guard, CsConditionSeq cGuard, CsAlgebra<S> alg, Func<S, string> inputToString = null)
        {
            return new CsLabel<S>(true, guard, cGuard, alg, null, inputToString);
        }

        public static CsLabel<S> MkTransitionLabel(CsPred<S> guard, CsConditionSeq cGuard, CsAlgebra<S> alg, CsUpdateSeq updates, Func<S, string> inputToString = null)
        {
            return new CsLabel<S>(false, guard, cGuard, alg, updates, inputToString);
        }

     
        public static CsLabel<S> MkWTrans(CsAlgebra<S> alg, int w)
        {
            var label = new CsLabel<S>(false, null, null, alg, null, null);
            label.weight = w;
            return label;
        }

        public override string ToString()
        {
            return ToString(false);
        }

        internal string ToString(bool debugmode)
        {
            if (Guard == null)
            {
                var v = "";
                if (weight != -Int16.MaxValue)
                    v += "[weight: " + this.weight + "]";
                return v;
            }
            var cases = Guard.ToArray();
            string cond = "";
            foreach (var psi in cases)
            {
                var pp = Guard.Algebra.LeafAlgebra as ICharAlgebra<S>;
                if (cond != "")
                    cond += ",\n";
                cond += (pp != null ? pp.PrettyPrint(psi.Item2) : psi.Item2.ToString());
                var countercond = (debugmode ? psi.Item1.ToString() : psi.Item1.ToString<S>(Guard.Algebra));
                if (countercond != SpecialCharacters.TOP.ToString())
                    cond += "/" + countercond;
            }

            if (isFinalCondition)
            {
                return cond;
            }
            else
            {
                string v = "";
                if(cond != "0" )
                    v+=cond;
                var upd = DescribeCounterUpdate(debugmode);
                if (upd != "")
                {
                    v += SpecialCharacters.IMPLIES + upd;
                }
                if(weight != -Int16.MaxValue)
                    v += "[weight: " + this.weight+"]";
                return v;
            }
        }

        private string DescribeCounterUpdate(bool debugmode)
        {
            if(Updates != null)
                return Updates.ToString(debugmode);
            return "";
        }
    }

    public enum CsUpdate
    {
        /// <summary>
        /// No update
        /// </summary>
        NOOP = 0,
        /// <summary>
        /// Target counter is set to 0
        /// </summary>
        ADD0 = 1,
        /// <summary>
        /// Target counter is set to 1
        /// </summary>
        ADD1 = 2,
        /// <summary>
        /// Target counter is set to 1
        /// </summary>
        ADD01 = 3,
        /// <summary>
        /// Source counter greater or equal lower bound is checked
        /// </summary>
        EXIT = 8,
        /// <summary>
        /// Source counter less than upper bound is checked and the value is incermented by 1
        /// </summary>
        INCR = 4,
        /// <summary>
        /// Source counter less than upper bound is checked and the value is incermented by 1
        /// </summary>
        INCR0 = 5,
        /// <summary>
        /// Source counter less than upper bound is checked and the value is incermented by 1
        /// </summary>
        INCR1 = 6,
        /// <summary>
        /// Source counter less than upper bound is checked and the value is incermented by 1
        /// </summary>
        INCR01 = 7,
        /// <summary>
        /// 
        /// </summary>
        ADD0_EXIT = 9,
        /// <summary>
        /// 
        /// </summary>
        ADD1_EXIT = 10,
        /// <summary>
        /// 
        /// </summary>
        ADD01_EXIT = 11,
        /// <summary>
        /// Source counter is in the middle
        /// </summary>
        INCR_EXIT = 12,
        /// <summary>
        /// 
        /// </summary>
        INCR0_EXIT = 13,
        /// <summary>
        ///
        /// </summary>
        INCR1_EXIT = 14,
        /// <summary>
        ///
        /// </summary>
        INCR01_EXIT = 15,
        /// <summary>
        /// Source counter greater or equal lower bound is checked and target counter is set to 1
        /// </summary>
        COPY = 16,
        COPY_ADD0 = 17,
        COPY_ADD1 = 18,
        COPY_ADD01 = 19,
        COPY_INCR = 20,
    }

    public enum CsCondition
    {
        /// <summary>
        /// Unsatisfiable condition
        /// </summary>
        FALSE = 0,
        /// <summary>
        /// Nonempty and all elements are below lower bound
        /// </summary>
        LOW = 1,
        /// <summary>
        /// Some element is at least lower bound but it is not the only element if it is the upper bound
        /// </summary>
        MIDDLE = 2,
        /// <summary>
        /// The condition when loop increment is possible, same as LOW|MIDDLE
        /// </summary>
        CANLOOP = 3,
        /// <summary>
        /// Singleton set containing the upper bound
        /// </summary>
        HIGH = 4,
        /// <summary>
        /// All elements are below lower bound, or singleton set containing the upper bound, same as LOW|HIGH
        /// </summary>
        LOWorHIGH = 5,
        /// <summary>
        /// The condition when loop exit is possible, same as MIDDLE|HIGH
        /// </summary>
        CANEXIT = 6,
        /// <summary>
        /// Set is nonempty, same as LOW|MIDDLE|HIGH
        /// </summary>
        NONEMPTY = 7,
        /// <summary>
        /// Set is empty
        /// </summary>
        EMPTY = 8,
        /// <summary>
        /// Same as EMPTY|LOW
        /// </summary>
        CANNOTEXIT = 9,
        /// <summary>
        /// Same as EMPTY|MIDDLE
        /// </summary>
        EMPTYorMIDDLE = 10,
        /// <summary>
        /// Same as EMPTY|MIDDLE|LOW
        /// </summary>
        EMPTYorCANLOOP = 11,
        /// <summary>
        /// Same as EMPTY|HIGH
        /// </summary>
        CANNOTLOOP = 12,
        /// <summary>
        /// Same as EMPTY|HIGH|LOW
        /// </summary>
        EMPTYorHIGHorLOW = 13,
        /// <summary>
        /// Same as EMPTY|HIGH|MIDDLE
        /// </summary>
        EMPTYorCANEXIT = 14,
        /// <summary>
        /// Condition that always holds, same as EMPTY|MIDDLE|HIGH|LOW
        /// </summary>
        TRUE = 15,
    }

    public class CsUpdateSeq
    {
        Tuple<int, ulong, ulong, ulong> vals;

        CsUpdateSeq(int count, ulong set0, ulong set1, ulong incr)
        {
            vals = new Tuple<int, ulong, ulong, ulong>(count, set0, set1, incr);
        }

        public static CsUpdateSeq MkNOOP(int count)
        {
            return new CsUpdateSeq(count, 0, 0, 0);
        }

        public int Length
        {
            get { return vals.Item1; }
        }

        public static CsUpdateSeq Mk(params CsUpdate[] vals)
        {
            ulong set0 = 0;
            ulong set1 = 0;
            ulong incr = 0;


            ulong bit = 1;

            for (int i = 0; i < vals.Length; i++)
            {
                if (vals[i].HasFlag(CsUpdate.ADD0))
                    set0 = set0 | bit;
                if (vals[i].HasFlag(CsUpdate.ADD1))
                    set1 = set1 | bit;
                if (vals[i].HasFlag(CsUpdate.INCR))
                    incr = incr | bit;
                bit = bit << 1;
            }
            return new CsUpdateSeq(vals.Length, set0, set1, incr);
        }

        public static CsUpdateSeq operator |(CsUpdateSeq left, CsUpdateSeq right)
        {
            if (left.vals.Item1 != right.vals.Item1)
                throw new ArgumentException("Incompatible lenghts");

            return new CsUpdateSeq(left.vals.Item1, left.vals.Item2 | right.vals.Item2, left.vals.Item3 | right.vals.Item3, left.vals.Item4 | right.vals.Item4);
        }

        public CsUpdate this[int i]
        {
            get
            {
                ulong bit = ((ulong)1) << i;
                int val = 0;
                if ((vals.Item2 & bit) != 0)
                    val = val | 1;
                if ((vals.Item3 & bit) != 0)
                    val = val | 2;
                if ((vals.Item4 & bit) != 0)
                    val = val | 4;




                CsUpdate res = (CsUpdate)val;
                return res;
            }
        }

        public CsUpdateSeq Or(int i, CsUpdate upd)
        {
            ulong bit = ((ulong)1) << i;
            ulong set0 = vals.Item2;
            ulong set1 = vals.Item3;
            ulong incr = vals.Item4;


            if (upd.HasFlag(CsUpdate.ADD0))
                set0 = set0 | bit;
            if (upd.HasFlag(CsUpdate.ADD1))
                set1 = set1 | bit;
            if (upd.HasFlag(CsUpdate.INCR))
                incr = incr | bit;




            CsUpdateSeq res = new CsUpdateSeq(vals.Item1, set0, set1, incr);
            return res;
        }

        public CsUpdateSeq Set(int i, CsUpdate upd)
        {
            ulong bit = ((ulong)1) << i;
            var mask = ~bit;
            ulong set0 = vals.Item2 & mask;
            ulong set1 = vals.Item3 & mask;
            ulong incr = vals.Item4 & mask;


            if (upd.HasFlag(CsUpdate.ADD0))
                set0 = set0 | bit;
            if (upd.HasFlag(CsUpdate.ADD1))
                set1 = set1 | bit;
            if (upd.HasFlag(CsUpdate.INCR))
                incr = incr | bit;

            CsUpdateSeq res = new CsUpdateSeq(vals.Item1, set0, set1, incr);
            return res;
        }

        /// <summary>
        /// Returns true if all counter operations are NOOP
        /// </summary>
        public bool IsNOOP
        {
            get
            {
                return (vals.Item2 == 0 && vals.Item3 == 0 && vals.Item4 == 0);
            }
        }

        public override string ToString()
        {
            string s = "";
            for (int i = 0; i < Length; i++)
                if (this[i] != CsUpdate.NOOP)
                    s += string.Format("{0}({1});", this[i], SpecialCharacters.c(i));
            return s;
        }

        internal string ToString(bool debugmode)
        {
            if (debugmode)
            {
                return ToString();
            }
            else
            {
                string s = "";
                for (int i = 0; i < Length; i++)
                {

                    
                    switch (this[i])
                    {
                        case CsUpdate.INCR:
                            {
                                s += string.Format("{0}++;", SpecialCharacters.c(i));
                                break;
                            }
                        case CsUpdate.INCR0:
                            {
                                s += string.Format("{0}++{{0}};", SpecialCharacters.c(i));
                                break;
                            }
                        case CsUpdate.INCR1:
                            {
                                s += string.Format("{0}++{{1}};", SpecialCharacters.c(i));
                                break;
                            }
                        case CsUpdate.INCR01:
                            {
                                s += string.Format("{0}++{{0,1}};", SpecialCharacters.c(i));
                                break;
                            }
                        case CsUpdate.ADD0:
                            {
                                s += string.Format("{0}{1}{{0}};", SpecialCharacters.c(i), SpecialCharacters.ASSIGN);
                                break;
                            }
                        case CsUpdate.ADD1:
                            {
                                s += string.Format("{0}{1}{{1}};", SpecialCharacters.c(i), SpecialCharacters.ASSIGN);
                                break;
                            }
                        case CsUpdate.ADD01:
                            {
                                s += string.Format("{0}{1}{{0,1}};", SpecialCharacters.c(i), SpecialCharacters.ASSIGN);
                                break;
                            }





                        default:
                            {
                                break;
                            }
                    }
                }
                return s;
            }
        }

        public override bool Equals(object obj)
        {
            return vals.Equals(((CsUpdateSeq)obj).vals);
        }

        public override int GetHashCode()
        {
            return vals.GetHashCode();
        }
    }

    public class CsConditionSeq
    {
        bool isAND;
        /// <summary>
        /// Returns true iff this sequence represents a conjunction
        /// </summary>
        public bool IsAND
        {
            get
            {
                return isAND;
            }
        }

        Tuple<int, ulong, ulong, ulong, ulong, ulong> elems;
        /// <summary>
        /// Number of conditions
        /// </summary>
        public int Length { get { return elems.Item1; } }
        internal ulong Mask { get { return elems.Item2; } }
        internal ulong Empty { get { return elems.Item3; } }
        internal ulong Low { get { return elems.Item4; } }
        internal ulong Middle { get { return elems.Item5; } }
        internal ulong High { get { return elems.Item6; } }


        CsConditionSeq(bool isAND, Tuple<int, ulong, ulong, ulong, ulong, ulong> elems)
        {
            this.isAND = isAND;
            this.elems = elems;
        }

        /// <summary>
        /// Make a sequence that corresponds to the conjunction of the individual counter conditions.
        /// </summary>
        /// <param name="vals">i'th element is the i'th counter condition</param>
        public static CsConditionSeq MkAND(params CsCondition[] vals)
        {
            return MkSeq(true, vals);
        }

        /// <summary>
        /// Make a sequence that corresponds to the disjunction of the individual counter conditions.
        /// </summary>
        /// <param name="vals">i'th element is the i'th counter condition</param>
        public static CsConditionSeq MkOR(params CsCondition[] vals)
        {
            return MkSeq(false, vals);
        }

        static CsConditionSeq MkSeq(bool isOr, CsCondition[] vals)
        {
            if (vals.Length > 64)
                throw new NotImplementedException("More than 64 counter support not implemented");

            int length = vals.Length;
            ulong mask = (length == 64 ? ulong.MaxValue : ((ulong)1 << length) - 1);
            ulong empty = 0;
            ulong low = 0;
            ulong middle = 0;
            ulong high = 0;
            ulong bitmask = 1;
            for (int i = 0; i < length; i++)
            {
                CsCondition cond = vals[i];
                if (cond.HasFlag(CsCondition.LOW))
                    low = low | bitmask;
                if (cond.HasFlag(CsCondition.MIDDLE))
                    middle = middle | bitmask;
                if (cond.HasFlag(CsCondition.HIGH))
                    high = high | bitmask;
                if (cond.HasFlag(CsCondition.EMPTY))
                    empty = empty | bitmask;
                bitmask = bitmask << 1;
            }
            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(length, mask, empty, low, middle, high);
            return new CsConditionSeq(isOr, elems);
        }

        /// <summary>
        /// Creates a conjunction with all individual counter conditions being TRUE
        /// </summary>
        public static CsConditionSeq MkTrue(int length)
        {
            CsCondition[] vals = new CsCondition[length];
            for (int i = 0; i < length; i++)
                vals[i] = CsCondition.TRUE;
            return MkAND(vals);
        }

        /// <summary>
        /// Creates a disjunction with all individual counter conditions being FALSE
        /// </summary>
        public static CsConditionSeq MkFalse(int length)
        {
            CsCondition[] vals = new CsCondition[length];
            for (int i = 0; i < length; i++)
                vals[i] = CsCondition.FALSE;
            return MkOR(vals);
        }

        /// <summary>
        /// Creates a conjunction with all individual counter conditions being FALSE
        /// </summary>
        public static CsConditionSeq MkFalseConj(int length)
        {
            CsCondition[] vals = new CsCondition[length];
            for (int i = 0; i < length; i++)
                vals[i] = CsCondition.FALSE;
            return MkAND(vals);
        }
        public override bool Equals(object obj)
        {
            var cond = obj as CsConditionSeq;
            if (cond == null)
                return false;
            else
                return cond.isAND == isAND && elems.Equals(cond.elems);
        }

        public override int GetHashCode()
        {
            return (isAND ? elems.GetHashCode() : elems.GetHashCode() << 1);
        }

        public static string DescribeCondition<S>(CsAlgebra<S> algebra, CsCondition cond, int i)
        {
            switch (cond)
            {
                case CsCondition.TRUE:
                    return SpecialCharacters.TOP.ToString();
                case CsCondition.FALSE:
                    return SpecialCharacters.BOT.ToString();
                case CsCondition.EMPTY:
                    return string.Format("{0}={1}", SpecialCharacters.c(i), SpecialCharacters.EMPTYSET);
                case CsCondition.NONEMPTY:
                    return string.Format("{0}{1}{2}", SpecialCharacters.c(i), SpecialCharacters.NEQ, SpecialCharacters.EMPTYSET);
                case CsCondition.LOW:
                    return string.Format("{0}{2}{3}{4}max({0})<{1}", SpecialCharacters.c(i), algebra.GetCounter(i).LowerBound, SpecialCharacters.NEQ, SpecialCharacters.EMPTYSET, SpecialCharacters.AND);
                  
                case CsCondition.HIGH:
                    return string.Format("{0}={{{1}}}", SpecialCharacters.c(i), algebra.GetCounter(i).UpperBound);


                case CsCondition.CANEXIT:
                    return string.Format("{0}{1}{2}", SpecialCharacters.c(i), SpecialCharacters.GEQ, algebra.GetCounter(i).LowerBound);

                case CsCondition.CANNOTEXIT:
                    return string.Format("{0}{1}{2}", SpecialCharacters.c(i), SpecialCharacters.NOTGEQ, algebra.GetCounter(i).LowerBound);

                case CsCondition.CANLOOP:
                    //return string.Format("{0}+1{1}{2}", SpecialCharacters.c(i), SpecialCharacters.NEQ, SpecialCharacters.EMPTYSET);
                    return string.Format("{0}x{1}{2}(x<{3})", SpecialCharacters.EXISTS, SpecialCharacters.IN, SpecialCharacters.c(i), algebra.GetCounter(i).UpperBound);

                case CsCondition.CANNOTLOOP:
                    //return string.Format("{0}+1{1}{2}", SpecialCharacters.c(i), "=", SpecialCharacters.EMPTYSET);
                    return string.Format("{0}x{1}{2}(x<{3})", SpecialCharacters.NOTEXISTS, SpecialCharacters.IN, SpecialCharacters.c(i), algebra.GetCounter(i).UpperBound);

                case CsCondition.MIDDLE:
                    return string.Format("{2}{4}{5}{6}{0}{1}max({2})<{3}", algebra.GetCounter(i).LowerBound, SpecialCharacters.LEQ, SpecialCharacters.c(i), algebra.GetCounter(i).UpperBound, SpecialCharacters.NEQ, SpecialCharacters.EMPTYSET, SpecialCharacters.AND);


                case CsCondition.LOWorHIGH:
                    return string.Format("({0}{1}{2})", DescribeCondition<S>(algebra, CsCondition.LOW, i), SpecialCharacters.OR, DescribeCondition<S>(algebra, CsCondition.HIGH, i));

               default:
                    return string.Format("{0}({1})", cond, SpecialCharacters.c(i));

            }
        }

        public override string ToString()
        {
            string s = "";
            if (isAND)
            {
                for (int i = 0; i < Length; i++)
                {
                    if (this[i] != CsCondition.TRUE)
                    {
                        if (s != "")
                            s += SpecialCharacters.AND;
                        s += string.Format("{0}({1})", this[i], SpecialCharacters.c(i));
                    }
                }
                if (s == "")
                    s = SpecialCharacters.TOP.ToString();
            }
            else
            {
                for (int i = 0; i < Length; i++)
                {
                    if (this[i] != CsCondition.FALSE)
                    {
                        if (s != "")
                            s += SpecialCharacters.OR;
                        s += string.Format("{0}({1})", this[i], SpecialCharacters.c(i));
                    }
                }
                if (s == "")
                    s = SpecialCharacters.BOT.ToString();
            }
            return s;
        }

        public string ToString<S>(CsAlgebra<S> algebra)
        {
            //return ToString();
            string s = "";
            if (isAND)
            {
                for (int i = 0; i < Length; i++)
                {
                    if (this[i] != CsCondition.TRUE)
                    {
                        if (s != "")
                            s += SpecialCharacters.AND;
                        s += DescribeCondition<S>(algebra, this[i], i);
                    }
                }
                if (s == "")
                    s = SpecialCharacters.TOP.ToString();
            }
            else
            {
                for (int i = 0; i < Length; i++)
                {
                    if (this[i] != CsCondition.FALSE)
                    {
                        if (s != "")
                            s += SpecialCharacters.OR;
                        s += DescribeCondition<S>(algebra, this[i], i);
                    }
                }
                if (s == "")
                    s = SpecialCharacters.BOT.ToString();
            }
            return s;
        }

        public CsCondition[] ToArray()
        {
            var list = new List<CsCondition>();
            var arr = new CsCondition[Length];
            for (int i = 0; i < Length; i++)
                arr[i] = this[i];
            return arr;
        }

        /// <summary>
        /// Returns the i'th condition
        /// </summary>
        /// <param name="i">must be between 0 and Length-1</param>
        public CsCondition this[int i]
        {
            get
            {
                if (i >= Length || i < 0)
                    throw new ArgumentOutOfRangeException();
                else
                {
                    ulong bitmask = ((ulong)1) << i;
                    int res = 0;
                    if ((Low & bitmask) != 0)
                        res = (int)CsCondition.LOW;
                    if ((Middle & bitmask) != 0)
                        res = res | (int)CsCondition.MIDDLE;
                    if ((High & bitmask) != 0)
                        res = res | (int)CsCondition.HIGH;
                    if ((Empty & bitmask) != 0)
                        res = res | (int)CsCondition.EMPTY;
                    return (CsCondition)res;
                }
            }

        }



        /// <summary>
        /// If conjunction, returns true if all conditions in the sequence are different from FALSE.
        /// If disjunction, returns true if some condition in the sequence is different from FALSE
        /// </summary>
        public bool IsSatisfiable
        {
            get
            {
                if (isAND)
                    return (Empty | Low | Middle | High) == Mask;

                else
                    return (Middle != 0 | Low != 0 | High != 0 | Empty != 0);

            }
        }

        /// <summary>
        /// If conjunction, returns true if all conditions in the sequence are TRUE.
        /// If disjunction, returns true if some condition in the sequence is TRUE.
        /// </summary>
        public bool IsValid
        {
            get
            {
                var mask = Mask;
                if (isAND)

                    return (Empty == mask && Low == mask && Middle == mask && High == Mask);
                else
                    return (mask & (~Empty | ~Low | ~Middle | ~High)) != mask;

            }
        }

        /// <summary>
        /// Create a conjunction sequence of two sequences that represent conjunctions
        /// </summary>
        public static CsConditionSeq operator &(CsConditionSeq left, CsConditionSeq right)
        {
            if (left.Length == right.Length && left.isAND && right.isAND)
            {
                int length = left.Length;
                ulong mask = left.Mask;
                ulong empty = left.Empty & right.Empty;
                ulong low = left.Low & right.Low;
                ulong middle = left.Middle & right.Middle;
                ulong high = left.High & right.High;
                var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(length, mask, empty, low, middle, high);
                var res = new CsConditionSeq(true, elems);
                return res;
            }
            else
                throw new InvalidOperationException("Incompatible arguments, & is only supported between conjunction sequences");
        }

        /// <summary>
        /// Create a disjunction sequence of two sequences that represent disjunctions
        /// </summary>
        public static CsConditionSeq operator |(CsConditionSeq left, CsConditionSeq right)
        {
            if (left.Length == right.Length)// && !left.isAND && !right.isAND)
            {
                int length = left.Length;
                ulong mask = left.Mask;
                ulong empty = left.Empty | right.Empty;
                ulong low = left.Low | right.Low;
                ulong middle = left.Middle | right.Middle;
                ulong high = left.High | right.High;
                var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(length, mask, empty, low, middle, high);
                var res = new CsConditionSeq(false, elems);
                return res;
            }
            else
                throw new InvalidOperationException("Incompatible arguments, | is only supported between disjunction sequences");
        }

        /// <summary>
        /// Complement the sequence from OR to AND and vice versa, 
        /// individual counter conditions are complemented.
        /// </summary>
        public static CsConditionSeq operator ~(CsConditionSeq arg)
        {
            int length = arg.Length;
            ulong mask = arg.Mask;
            ulong empty = mask & ~arg.Empty;
            ulong low = mask & ~arg.Low;
            ulong middle = mask & ~arg.Middle;
            ulong high = mask & ~arg.High;
            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(length, mask, empty, low, middle, high);
            var res = new CsConditionSeq(!arg.isAND, elems);
            return res;
        }

        public CsConditionSeq Update(int i, CsCondition cond)
        {
            if (i >= Length)
                throw new ArgumentOutOfRangeException();

            ulong bit = ((ulong)1) << i;
            ulong bitmask = ~bit;
            //clear the bit
            ulong empty = Empty & bitmask;
            ulong low = Low & bitmask;
            ulong mid = Middle & bitmask;
            ulong high = High & bitmask;
            //set the new value
            if (cond.HasFlag(CsCondition.LOW))
                low = low | bit;
            if (cond.HasFlag(CsCondition.MIDDLE))
                mid = mid | bit;
            if (cond.HasFlag(CsCondition.HIGH))
                high = high | bit;
            if (cond.HasFlag(CsCondition.EMPTY))
                empty = empty | bit;

            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(Length, Mask, empty, low, mid, high);
            return new CsConditionSeq(isAND, elems);
        }

        /// <summary>
        /// Update the i'th element to this[i] | cond
        /// </summary>
        public CsConditionSeq Or(int i, CsCondition cond)
        {
            if (i >= Length)
                throw new ArgumentOutOfRangeException();

            ulong bit = ((ulong)1) << i;
            ulong empty = Empty;
            ulong low = Low;
            ulong mid = Middle;
            ulong high = High;
            //set the new value
            if (cond.HasFlag(CsCondition.LOW))
                low = low | bit;
            if (cond.HasFlag(CsCondition.MIDDLE))
                mid = mid | bit;
            if (cond.HasFlag(CsCondition.HIGH))
                high = high | bit;
            if (cond.HasFlag(CsCondition.EMPTY))
                empty = empty | bit;

            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(Length, Mask, empty, low, mid, high);
            var res = new CsConditionSeq(isAND, elems);
            return res;
        }

        /// <summary>
        /// Update the i'th element to this[i] & cond
        /// </summary>
        public CsConditionSeq And(int i, CsCondition cond)
        {
            if (i >= Length)
                throw new ArgumentOutOfRangeException();

            ulong bit = ((ulong)1) << i;
            ulong bit_false = ~bit;

            ulong empty = Empty;
            ulong low = Low;
            ulong mid = Middle;
            ulong high = High;
            //set the new value
            if (!cond.HasFlag(CsCondition.LOW))
                low = low & bit_false;
            if (!cond.HasFlag(CsCondition.MIDDLE))
                mid = mid & bit_false;
            if (!cond.HasFlag(CsCondition.HIGH))
                high = high & bit_false;
            if (!cond.HasFlag(CsCondition.EMPTY))
                empty = empty & bit_false;

            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(Length, Mask, empty, low, mid, high);
            var res = new CsConditionSeq(isAND, elems);
            return res;
        }

        public CsConditionSeq UpdateConditions(BasicCountingSet[] q, int i, ICounter[] counters)
        {
            ulong bit = ((ulong)1) << i;
            ulong bitmask = ~bit;
            //clear the bit
            ulong empty = Empty & bitmask;
            ulong low = Low & bitmask;
            ulong mid = Middle & bitmask;
            ulong high = High & bitmask;
            var cond = q[i];
            //set the new value
            if (cond.HasFlag(CsCondition.LOW, counters[i]))
                low = low | bit;
            else if (cond.HasFlag(CsCondition.MIDDLE, counters[i]))
                mid = mid | bit;
            else if (cond.HasFlag(CsCondition.HIGH, counters[i]))
                high = high & bit;
            else if (cond.HasFlag(CsCondition.EMPTY, counters[i]))
                empty = empty & bit;

            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(Length, Mask, empty, low, mid, high);
            return new CsConditionSeq(isAND, elems);
        }
        public static CsConditionSeq GetConditions(BasicCountingSet[] vals, List<int> activeCounters, ICounter[] counters)
        {
            if (vals.Length > 64)
                throw new NotImplementedException("More than 64 counter support not implemented");

            int length = vals.Length;
            ulong mask = (length == 64 ? ulong.MaxValue : ((ulong)1 << length) - 1);
            ulong low = 0;
            ulong middle = 0;
            ulong high = 0;
            ulong empty = 0;
            ulong bitmask = 1;
            for (int j = 0; j < activeCounters.Count(); j++)
            {
                int i = activeCounters[j];
                BasicCountingSet cond = vals[i];
                if (cond.HasFlag(CsCondition.LOW, counters[i]))
                    low = low | bitmask;
                else if (cond.HasFlag(CsCondition.MIDDLE, counters[i]))
                    middle = middle | bitmask;
                else if (cond.HasFlag(CsCondition.HIGH, counters[i]))
                    high = high | bitmask;
                else if (cond.HasFlag(CsCondition.EMPTY, counters[i]))
                    empty = empty | bitmask;
                bitmask = bitmask << 1;
            }
            var elems = new Tuple<int, ulong, ulong, ulong, ulong, ulong>(length, mask, empty, low, middle, high);
            return new CsConditionSeq(true, elems);
        }
        /// <summary>
        /// Creates a conjunction with all individual counter conditions being LOW
        /// </summary>
        public static CsConditionSeq InitForLow(int length)
        {
            CsCondition[] vals = new CsCondition[length];
            for (int i = 0; i < length; i++)
                vals[i] = CsCondition.LOW;
            return MkAND(vals);
        }


        /// <summary>
        /// Returns the i'th condition
        /// </summary>
        /// <param name="i">must be between 0 and Length-1</param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int CountIndex(int[] activeCounters)
        {
            int res = 0;
            var ac = new List<int>();
            for (int c = 0; c < activeCounters.Length; c++)
            {
                int i = activeCounters[c];
             
                ulong bitmask = ((ulong)1) << i;
                if ((Low & bitmask) != 0)
                    res = res | (int)(CsCondition.LOW) << c * 2;
                if ((Middle & bitmask) != 0)
                    res = res | (int)(CsCondition.MIDDLE) << c * 2;
                if ((High & bitmask) != 0)
                    res = res | (int)(CsCondition.CANLOOP) << c * 2;
            }
            return (int)res;
        }
    }
}

