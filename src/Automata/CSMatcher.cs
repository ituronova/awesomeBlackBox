using System;
using System.Collections;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Automata 
{
    public class CSState
    {
        public int[] cash = null;
        public Tuple<int, BasicCountingSet[]> conf;

        public CSState(Tuple<int, BasicCountingSet[]> conf)
        {
            var bs = new BasicCountingSet[conf.Item2.Count()];
          /*  for (int i = 0; i < conf.Item2.Count(); i++)
            {
                bs[i] = conf.Item2[i].Clone();
            }*/
            this.conf = new Tuple<int, BasicCountingSet[]>(conf.Item1, bs);
            this.cash = new int[255];
        }

        public void CreateTransition(int c, int p)
        {
            if (c < 255)
                this.cash[c] = p;
            else
                throw new ArgumentException("Minterm out of the range of the state array.");
        }

        public bool Equals(Tuple<int, BasicCountingSet[]> conf)
        {
            if(conf.Item1 == this.conf.Item1)
            {
                for (int i = 0; i < conf.Item2.Count(); i++)
                {
                    if (!this.conf.Item2[i].Equals(conf.Item2[i]))
                        return false;
                }
                return true;                
            }
            return false;
        }
    }

    public class CSMatcher
    {
        //public CSState[] states;
        public int[] states;
        public int[][] next;
        public Hashtable ht;
        
        public int countStates;
        public int hit = 0;
        public int miss = 0;
        
        public CSMatcher()
        {
            this.ht = new Hashtable();
        }

        public int CreateState(Tuple<int, BasicCountingSet[]> conf)
        {
           
            // this.states[this.countStates] = new CSState(conf);
            this.ht.Add(conf, this.countStates);
            this.countStates++;
            if (countStates >= 1000000)
                throw new Exception("Number of states of matcher automata reached maximum.");
            return countStates - 1;
        }

        public void CreateTransition(int s, int t, int c)
        {
           /*var nextState = this.states[s].cash[c];
           if(nextState == 0)
            this.states[s].CreateTransition(c, t);  */       
        }
        

        public int GetState(Tuple<int, BasicCountingSet[]> conf)
        {
            // start with state = 1
            for (var s = 1; s < this.countStates; s++)
            {
                if (states[s].Equals(conf))
                    return s;
            }
            // else create new state
            return this.CreateState(conf);
        }


        public Tuple<int, BasicCountingSet[]> GetNext(int p, int c)
        {
            try
            {
                //var next = this.states[p].cash[c];
                var next = 0;
                if (next == 0)
                    return null;
                //var nextBS = this.states[next].conf.Item2;
                //var bs = new BasicCountingSet[nextBS.Count()];
                /* for (int i = 0; i < nextBS.Count(); i++)
                 {
                     bs[i] = nextBS[i].Clone();
                 }*/
                //return new Tuple<int, BasicCountingSet[]>(this.states[next].conf.Item1, bs);
                return null;
            }
            catch
            {
                return null;
            }
        }
    }
}
