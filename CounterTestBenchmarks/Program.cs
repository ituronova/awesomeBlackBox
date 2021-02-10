using Microsoft.Automata;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Globalization;


namespace CounterAutomataBench
{
    public enum Version
    {
        /// <summary>
        /// Margus version of the algorithm
        /// </summary>
        MARGUS = 0,
        /// <summary>
        /// Our version of the algorithm
        /// </summary>
        CHIPMUNK = 1,
        /// <summary>
        /// Both our and Margus version of the algorithm
        /// </summary>
        BOTH = 2,
        /// <summary>
        /// .NET regex
        /// </summary>
        REGEX = 3,
    }
    class Stats
    {
        List<string> header = new List<string>();
        Dictionary<string, List<string>> columns = new Dictionary<string, List<string>>();

        public void Add(string name, string value)
        {
            List<string> column;
            if (!columns.TryGetValue(name, out column))
            {
                header.Add(name);
                column = new List<string>();
                columns[name] = column;
            }
            if (value == double.NaN.ToString())
                column.Add(string.Empty);
            else
                column.Add(value);
        }

        public void Validate()
        {
            if (header.Count > 0)
            {
                Debug.Assert(columns.Count == header.Count);
                Debug.Assert(header.All(x => columns.ContainsKey(x)));
                Debug.Assert(columns.All(x => x.Value.Count == columns[header[0]].Count));
            }
        }

        public void WriteTSV(string path)
        {
            Validate();
            
            if (File.Exists(path))
            {
                File.Delete(path);
            }
            using (var fout = new StreamWriter(new FileStream(path, FileMode.CreateNew)))
            {
                Func<string, string, string> csvJoin = (l, r) => $"{l}\t{r}";

                fout.WriteLine(header.Aggregate(csvJoin));

                var rows = header.Select(x => columns[x]).Aggregate((c1, c2) => c1.Zip(c2, csvJoin).ToList());
                foreach (var row in rows)
                {
                    fout.WriteLine(row);
                }
            }
        }
    }

    class Stat : IDisposable
    {
        Stats stats;
        String name;

        public Stat(Stats stats, string name)
        {
            this.stats = stats;
            this.name = name;
        }

        public void Dispose()
        {
            stats.Add(name, this.ToString());
        }
    }

    class HotAverage : Stat
    {
        List<double> samples = new List<double>();

        public HotAverage(Stats stats, string name) : base(stats, name)
        {
        }

        public void Add(double value)
        {
            samples.Add(value);
        }

        public override string ToString()
        {
            double average = double.NaN;
            if (samples.Count == 1)
            {
                average = samples[0];
            }
            else if (samples.Count > 1)
            {
                average = (samples.Sum() - samples[0]) / (samples.Count - 1);
            }
            return average.ToString();
        }
    }

    class Message : Stat
    {
        string message = "";

        public Message(Stats stats, string name) : base(stats, name)
        {
        }

        public void Add(string newMessage)
        {
            message += newMessage.Replace("\r", "\\r").Replace("\n", "\\n").Replace("\t", "\\t");
        }

        public override string ToString()
        {
            return message;
        }
    }

    class Exact<T> : Stat where T : struct, IEquatable<T>
    {
        T? value;

        public Exact(Stats stats, string name) : base(stats, name)
        {
        }

        public void Add(T newValue)
        {
            if (value != null)
            {
                Debug.Assert(newValue.Equals(value.Value));
            }
            value = newValue;
        }

        public override string ToString()
        {
            var v = value.ToString();
            return value.ToString();
        }
    }

    class Program
    {
        const int SAMPLES = 1;
        const int TIMEOUT = 60000;   // 1 min
        const int MAXSAMPLES = 1;   // number of samples for validating the automata

        static IEnumerable<string> ReadRegexes(string path)
        {
            using (var fin = new StreamReader(new FileStream(path, FileMode.Open)))
            {
                string regex;
                while ((regex = fin.ReadLine()) != null)
                {
                    yield return regex;
                }
            }
        }

        static string[] ReadText(string path)
        {
            return System.IO.File.ReadAllLines(path);
        }

        static void WriteRegexes(string path, string[] regexes)
        {
            using (var fout = new StreamWriter(new FileStream(path, FileMode.Create)))
            {
                foreach (var regex in regexes)
                {
                    fout.WriteLine(regex);
                }
            }
        }


       
        bool IsMonadic(string regex)
        {
            Predicate<SymbolicRegexNode<ulong>> isNonMonadic = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop &&
                        node.Left.Kind != SymbolicRegexKind.Singleton &&
                        !node.IsStar &&
                        !node.IsMaybe &&
                        !node.IsPlus);
            };

            var sr = new Regex(regex, RegexOptions.Singleline);
            SymbolicRegexUInt64 m = null;
            m = sr.Compile(true, false) as SymbolicRegexUInt64;
            return (!m.Pattern.ExistsNode(isNonMonadic));
        }

    /*    static string[] FilterRegexes(string[] regexes, out List<string> notSupported, out List<string> nonMonadic, out List<string> noCounters, out List<string> simpleStrings, out List<string> nestedCounters, out List<string> notnestedCounters, bool banchmark_mode = false, bool filter_mode = true, bool decode_mode = false)
        {


            Predicate<SymbolicRegexNode<ulong>> isNonMonadic = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop &&
                        node.Left.Kind != SymbolicRegexKind.Singleton &&
                        !node.IsStar &&
                        !node.IsMaybe &&
                        !node.IsPlus);
            };

            Predicate<SymbolicRegexNode<ulong>> isCountingLoop = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop &&
                        !node.IsStar &&
                        !node.IsMaybe &&
                        !node.IsPlus);
            };

            Predicate<SymbolicRegexNode<ulong>> isNestedCounter = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop && node.Left.ExistsNode(isCountingLoop));
            };


            var filtered = new List<string>();
            notSupported = new List<string>();
            nonMonadic = new List<string>();
            noCounters = new List<string>();
            simpleStrings = new List<string>();
            nestedCounters = new List<string>();
            notnestedCounters = new List<string>();
            var i = 0;


            foreach (var str in regexes)
            {
                string reasonwhynot = "";
                string rgx = "";
                if (decode_mode)
                    rgx = str.Replace("\\n", "n");
                else
                    rgx = str;
                try
                {
                    // decode regular expression (remove double blackslash and remove curly brackets)
                    string regex = "";
                    if (decode_mode)
                        regex = Decode(rgx);
                    else
                        regex = rgx;
                    i++;
                    if (filter_mode)
                    {
                        Console.WriteLine("Filtering...");
                        Console.WriteLine(regex);
                        Console.Write(i + "\n");

                        var sr = new Regex(regex, RegexOptions.Singleline);
                        SymbolicRegexUInt64 m = null;
                        if (sr.IsCompileSupported(out reasonwhynot))
                        {
                            try
                            {
                                m = sr.Compile(true, false) as SymbolicRegexUInt64;
                            }
                            catch (Exception e)
                            {
                                notSupported.Add(rgx + "\t" + e.Message);
                                continue;
                            }
                            if (!m.Pattern.ExistsNode(isCountingLoop))
                            {
                                noCounters.Add(rgx);    // store original string
                            }
                            else if (m.Pattern.ExistsNode(isNonMonadic))
                            {
                                nonMonadic.Add(rgx);    // store original string
                                if (m.Pattern.ExistsNode(isNestedCounter))
                                {
                                    nestedCounters.Add(rgx);
                                }
                                else
                                    notnestedCounters.Add(rgx);
                            }
                            else
                                filtered.Add(regex);    // store decoded string
                        }
                        else
                            notSupported.Add(rgx + "\t" + reasonwhynot);
                    }
                    else
                        filtered.Add(regex);    // store decoded string     
                }
                catch (Exception e)
                {
                    // TODO: how to indicate single strings?
                    if (e.Source == "CounterAutomataBench" && e.Message == "Odkaz na objekt není nastaven na instanci objektu.")
                        simpleStrings.Add(rgx);
                    else
                        notSupported.Add(rgx + "\t" + e.Message);
                    Console.WriteLine("Error in filtering.");
                }
            }
            return filtered.ToArray();
        }*/

        static int IsMonadicExpr(string str)
        {
            Predicate<SymbolicRegexNode<ulong>> isNonMonadic = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop &&
                        node.Left.Kind != SymbolicRegexKind.Singleton &&
                        !node.IsStar &&
                        !node.IsMaybe &&
                        !node.IsPlus);
            };

            Predicate<SymbolicRegexNode<ulong>> isCountingLoop = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop &&
                        !node.IsStar &&
                        !node.IsMaybe &&
                        !node.IsPlus);
            };

            Predicate<SymbolicRegexNode<ulong>> isNestedCounter = node =>
            {
                return (node.Kind == SymbolicRegexKind.Loop && node.Left.ExistsNode(isCountingLoop));
            };
            try
            {
                // decode regular expression (remove double blackslash and remove curly brackets)
                string regex = "";
                var sr = new Regex(regex, RegexOptions.Singleline);
                SymbolicRegexUInt64 m = null;
                string error;
                if (sr.IsCompileSupported(out error))
                {
                    try
                    {
                        m = sr.Compile(false, false) as SymbolicRegexUInt64;
                    }
                    catch (Exception e)
                    {
                        Console.WriteLine("Error in compilation.");
                        return -1;
                    }
                    if (m.Pattern.ExistsNode(isNonMonadic))
                    {
                        if (m.Pattern.ExistsNode(isNestedCounter))
                        {
                            return 0;
                        }
                        else
                            return 0;
                    }
                }
                else
                {
                    Console.WriteLine("Expression is not supported.");
                    return -1;
                }
            }
            catch (Exception e)
            {
                Console.WriteLine("Expression is not supported.");
                return -1;
            }
            return 1;
        }



        //static void BenchmarkFile(string path, bool benchmark_mode, bool filter_mode, bool decode_mode, bool runOur, bool runClassical, bool runValidate, bool runMy, bool runAlgebra, bool runOptimal)
        static void Main(string[] args)
        {
            int count = 0;
            
            Regex rgx = new Regex(args[1], RegexOptions.Singleline);
            var pattern = ((SymbolicRegex<ulong>)rgx.Compile(false, false));
            var nca = pattern.Pattern.CreateCountingAutomatonPushIncr(false);
            var dca = nca.CompileOpt(1);
            var stats = new Stats();

            // init counting sets
            if (dca.cntCount != 0)
            {   // initialize counting sets
                dca.cs = new BasicCountingSet[dca.cntCount];
                for (int j = 0; j < dca.cntCount; j++)
                {
                    dca.cs[j] = new BasicCountingSet(dca.counters[j]);    // initialization to 0   
                }
            }

             using (StreamReader sr = File.OpenText(args[2]))
             {
                 string s = String.Empty;
                while ((s = sr.ReadLine()) != null)
                {
                    using (var exception = new Message(stats, "Our exception"))
                    using (var dcaTimeouts = new Exact<int>(stats, "Timeouts"))
                    using (var dcaCounters = new Exact<long>(stats, "Counters-DCA"))
                    using (var ncaCounters = new Exact<int>(stats, "Counters-NCA"))
                    using (var dcaTrans = new Exact<int>(stats, "DCA-trans"))
                    using (var ncaTrans = new Exact<int>(stats, "NCA-trans"))
                    using (var dcaSize = new Exact<int>(stats, "|DCA|"))
                    using (var ncaSize = new Exact<int>(stats, "|NCA|"))
                    using (var ncaToDca = new HotAverage(stats, "NCA->DCA (milliseconds)"))
                    using (var srToNca = new HotAverage(stats, "SR->NCA (milliseconds)"))
                    using (var rgxToSR = new HotAverage(stats, "regex->SR (milliseconds)"))
                    {
                        if (pattern.IsMatchCA(s, dca))
                        {
                            count++;
                        }
                    }
                 }
             }

            Console.WriteLine("Time: 0");
            Console.WriteLine("Matching lines: " + count);
            Console.Read();
        }
    }
}
