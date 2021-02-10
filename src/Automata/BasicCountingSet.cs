using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading.Tasks;


namespace Microsoft.Automata
{
    public class symbConf
    {
        readonly ValueTuple<int, int, int[], int, int, int, int> SC;

        public ValueTuple<int, int, int[], int, int, int, int> cs
        {
            get
            {
                return SC;
            }
        }

        public symbConf(BasicCountingSet cs, ICounter c)
        {
            int[] basicSet = null;
            try
            {
                basicSet = cs.CreateSymbCS();
            }
            catch
            {
                Console.WriteLine("Error is in symbol.\n");
            }
            try
            {
                SC = ValueTuple.Create(cs.Max(), cs.CountElements(), basicSet, cs.upperBound, c.LowerBound, cs.flag, cs.Min());
            }
            catch(Exception e)
            {
                Console.WriteLine("Error while creating.\n");
            }
        }

        public symbConf(symbConf cs)
        {
            var basicSet = new int[cs.Count()];
            for(int i = 0; i < cs.Count(); i++)
            {
                basicSet[i] = cs.CSet()[i];
            }
            SC = ValueTuple.Create(cs.Max(), cs.Count(), basicSet, cs.upperBound(), cs.lowerBound(), cs.Flag(), cs.Min());
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool Equals(symbConf sc)
        {
            if (sc.Count() == this.Count()) 
            {
                if (sc.Max() == this.Max())
                {
                    if (sc.Min() == this.Min())
                    {
                        for (int i = 0; i < this.Count(); i++)
                        {
                            if (sc.CSet()[i] != this.CSet()[i])
                                return false;
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Max()
        {
            return SC.Item1;
        }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Count()
        {
            return SC.Item2;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int[] CSet()
        {
            return SC.Item3;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int upperBound()
        {
            return SC.Item4;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int lowerBound()
        {
            return SC.Item5;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Flag()
        {
            return SC.Item6;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Min()
        {
            return SC.Item7;
        }

        public override string ToString()
        {
            var s = "";
            for (int i = 0; i < this.SC.Item2; i++)
                s += this.SC.Item3[i].ToString() + " ";
            return s;
        }

    }

    /// <summary>
    /// Implements a bounded set on integers that supports incermenting all elements adding 0 and 1.
    /// </summary>
    public class BasicCountingSet : ICountingSet
    {
        /// <summary>
        /// Upper limit on what the maximum value in the set can be.
        /// </summary>
        public int upperBound;
        int size;
        int start;
        int end;
        public int[] basicSet;
        int offset;
        public int flag;

        public BasicCountingSet CopyIt(BasicCountingSet bs)
        {
            bs.upperBound = this.upperBound;
            bs.size = this.upperBound + 2;
            size = size > 10000 ? 10000 : size;
            bs.basicSet = new int[size];
            for (int i = 0; i < size; i++)
                bs.basicSet[i] = this.basicSet[i];
            bs.start = this.start;
            bs.end = this.end;
            bs.offset = this.offset;
            bs.flag = this.flag;
            return bs;
        }

        public bool Equals(BasicCountingSet sc)
        {
            
            if(sc.IsEmpty())
            {
                if (this.IsEmpty())
                    return true;
                else
                    return false;
            }
            if (sc.Max() == this.Max()) 
            {
                if (sc.CountElements() == this.CountElements())
                {
                    int j = sc.end;
                    for (int i = end; i%size != start; i++)
                    {
                        if ((offset - basicSet[i % size]) != (sc.offset - sc.basicSet[j % sc.size]))
                            return false;
                        j++;
                    }
                    return true;
                }
            }
            return false;
        }


        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void SetInitFlag(ICounter counter)
        {
            if (counter.LowerBound != 0)
                this.flag = (int)CsCondition.LOW;
            else
                this.flag = (int)CsCondition.MIDDLE;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void SetInitFlag(int value)
        {
            if (value != 0)
                this.flag = (int)CsCondition.LOW;
            else
                this.flag = (int)CsCondition.MIDDLE;
        }


        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool HasFlag(CsCondition flag, ICounter counter)
        {
            switch (flag)
            {
                case CsCondition.LOW:
                    if (this.Max() < counter.LowerBound)
                        return true;
                    break;
                case CsCondition.MIDDLE:
                    if (this.Max() >= counter.LowerBound && !(this.IsSingleton() && this.Max() == counter.UpperBound))
                        return true;
                    break;
                case CsCondition.HIGH:
                    if (this.IsSingleton() && this.Max() == counter.UpperBound)
                        return true;
                    break;
            }
            return false;
        }

        /// <summary>
        /// True iff the counting set is empty.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool IsEmpty()
        {
            return start == end;
        }

        /// <summary>
        /// True iff the counting set is a singleton set.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool IsSingleton()
        {
            return start == (end + 1) % size;
        }

        /// <summary>
        /// True iff the counting set is full.
        /// </summary>
        public bool IsFull()
        {
            return (start + 1) % size == end;
        }

        public int CountElements()
        {
            return (start + this.size - end) % size;
        }


        
        public BasicCountingSet(symbConf c)
        {
            this.upperBound = c.upperBound();
            this.size = c.upperBound() + 2;
            // limit cs for 10000
            this.size = size > 10000 ? 10000 : size;
            this.basicSet = new int[size];
            int max = c.CSet().Max();
            for(int i = 0; i < c.Count(); i++)
                this.basicSet[i] = max - c.CSet()[i];
            this.start = c.Count();
            this.end = 0;
            this.offset = max;
            this.SetInitFlag(c.lowerBound());
        }

        /// <summary>
        /// Create a counting set, max is the maximum element size, max must be at least 2 and initialize it to 0.
        /// </summary>
        public BasicCountingSet(ICounter c)
        {
            this.upperBound = c.UpperBound;

            this.size = c.UpperBound + 2;
            // limit cs for 10000
            this.size = size > 10000 ? 10000 : size;
            this.basicSet = new int[size];
            this.basicSet[start] = 0;
            this.start = 1;
            this.end = 0;
            this.offset = 0;
            this.SetInitFlag(c);
        }

     
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool IsAbove()
        {
            if (this.Max() > this.upperBound)
                return true;
            return false;
        }

        /// <summary>
        /// Gets the maximum value in the set. Set must be nonempty.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Max()
        {
           return offset - basicSet[end];
        }

        /// <summary>
        /// Gets the minimum value in the set. Set must be nonempty.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public int Min()
        {
            return offset - basicSet[(start + size - 1) % size];
        }

        /// <summary>
        /// Set the counting set to the value [0].
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Set0()
        {
            this.basicSet[0] = 0;
            start = 1;
            end = 0;
            this.offset = 0;
        }

        /// <summary>
        /// Set the counting set to the value [1].
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Set1()
        {
            this.basicSet[0] = 0;
            start = 1;
            end = 0;
            this.offset = 1;
        }


        /// <summary>
        /// Increment all values in the set.
        /// If Max becomes greater than UpperBound then remove it.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Incr()
        {
            /*   if (offset - basicSet[end] == this.upperBound)
               {
                   //remove the first element
                   end = (end + 1) % size;
                   if (this.IsEmpty())
                       Clear();
                   else
                       offset += 1;
               }
               else
                   offset += 1;*/
            if (offset - basicSet[end] >= this.upperBound)
            {
                //remove the first element
                end = (end + 1) % size;
                if (this.IsEmpty())
                    Clear();
            }
            offset += 1;
           
        }

        /// <summary>
        /// Push 0 into the set.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Push0()
        {
            if (basicSet[(start + size - 1) % size] != offset)
            {
                basicSet[start] = offset;
                start = (start + 1) % size;
            }
        }

       


        /// <summary>
        /// Push 1 into the set.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Push1()
        {
            if (this.IsEmpty())
            {
                basicSet[start] = 0;
                start = 1;
                offset = 1;
            }
            else if (offset - basicSet[end] == 0)  // maximum is equal to 0
            {
                // only increment 0
                if (offset - basicSet[end] == upperBound)
                {
                    //remove the first element
                    end = (end + 1) % size;
                    if (this.IsEmpty())
                        Clear();
                    else
                        offset += 1;
                }
                else
                    offset += 1;
                if (basicSet[(start + size - 1) % size] != offset)
                {
                    basicSet[start] = offset;
                    start = (start + 1) % size;
                }
            }
            else if (offset - basicSet[end] == 1 || this.Min() == 1)  // maximum or minimum is equal to 1
            {
                return;
            }
            else if(this.CountElements() == 1)  // one element other than 0 or 1
            {
                basicSet[start] = offset - 1;
                start = (start + 1) % size;
                var c = CountElements();
            }
            else
            {
                throw new Exception("Push 1 to basic set with more elements.");             
            }
        }

        /// <summary>
        /// Empty the set.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Clear()
        {
            basicSet[0] = 0;
            start = 1;
            end = 0;
            offset = 0;
        }

        /// <summary>
        /// Increment all values in the set and push 0 into the set.
        /// If Max becomes greater than UpperBound then remove it.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void IncrPush0()
        {
            // check maximum
            if (offset - basicSet[end] >= upperBound)
            {
                //remove the first element
                end = (end + 1) % size;
                if (this.IsEmpty())
                    Clear();
            }
            // increment
            offset += 1; 
            // push 0   
            if (basicSet[(start + size - 1) % size] != offset)
            {
                basicSet[start] = offset;
                start = (start + 1) % size;
            }
           
        }

        /// <summary>
        /// Increment all values in the set and push 1 into the set.
        /// If Max becomes greater than UpperBound then remove it.
        /// </summary>

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void IncrPush1()
        {
            if (offset - basicSet[end] == upperBound)
            {
                //remove the first element
                end = (end + 1) % size;
                if (this.IsEmpty())
                    Clear();
            }
            if (basicSet[(start + size - 1) % size] != offset)
            {
                basicSet[start] = offset;
                start = (start + 1) % size;
            }
            offset += 1;
            /*if (offset - basicSet[end] == upperBound)
            {
                //remove the first element
                end = (end + 1) % size;
                if (this.IsEmpty())
                    Clear();
                else
                    offset += 1;
            }
            else
                offset += 1;*/
        }

        /// <summary>
        /// Increment all values in the set and push 0 and 1 into the set.
        /// If Max becomes greater than UpperBound then remove it.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void IncrPush01()
        {
            if (basicSet[(start + size - 1) % size] != offset)
            {
                basicSet[start] = offset;
                start = (start + 1) % size;
            }
            if (offset - basicSet[end] == upperBound)
            {
                //remove the first element
                end = (end + 1) % size;
                if (this.IsEmpty())
                    Clear();
                else
                    offset += 1;
            }
            else
                offset += 1;
            if (basicSet[(start + size - 1) % size] != offset)
            {
                basicSet[start] = offset;
                start = (start + 1) % size;
            }
        }



        public int[] CreateSymbCS()
        {
            var s = new int[this.CountElements()];
            int j = 0;
            for (int i = end; i % size != start; i++)
            {
                try
                {
                    s[j] = offset - basicSet[(i % size)];
                    j += 1;
                }
                catch
                {
                    Console.WriteLine("Error is here.\n");
                }
            }
            return s;
        }

        /// <summary>
        /// Returns decimal representation of the elements in the set in decreasing order.
        /// </summary>
        public override string ToString()
        {
            var s = "[";      
            for (int i = end; i % size != start; i++)
            {
                if (s != "[")
                    s += ",";
                s += (offset - basicSet[(i % size)]).ToString();
            }
            s += "]";
            return s;
        }

        public int[] ToArray()
        {
            var s = new int[this.CountElements()];
            int j = 0;
            for (int i = end; i % size != start; i++)
            {
                s[j] = (offset - basicSet[(i % size)]);
                j++;
            }
            return s;
        }
    }
}
