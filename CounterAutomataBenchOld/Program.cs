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
            CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;

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

        static IEnumerable<string> ReadText(string path)
        {
           // Console.WriteLine(path);
            try
            {
                return System.IO.File.ReadAllLines(path);
            }
            catch
            {
                Console.WriteLine("File "+path+" not found.");
            }
            return new List<string>();
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

        //static Stats Benchmark(string[] regexes, string[] nonMonadic, bool runOur = true, bool runClassical = true, bool runValidate = false, bool runMy = true, bool runAlgebra = false, bool runOptimal = false)
        static Stats Benchmark(string regex, List<string> text, out double time, out int count, Version version)
        {
            var stats = new Stats();
            count = 0;
            time = 0;
            int countMatch = 0;
            double t = 0;
            CsAutomatonOpt<ulong> dca = null;
            CountingAutomaton<ulong> nca = null;
            SymbolicRegex<ulong> pattern = null;
            HashSet<string> samples = new HashSet<string>();
            HashSet<string> negSamples = new HashSet<string>();
            Regex rgx = new Regex(regex, RegexOptions.Singleline);
            stats.Add("pattern", regex);

            Stopwatch sw = new Stopwatch();
            if(version != Version.REGEX)
            {
                try
                {
                    double ncaTime = 0;
                    //---------------------------------------    
                    // COUNTING SETS APPROACH
                    //---------------------------------------
                    sw.Restart();
                    pattern = ((SymbolicRegex<ulong>)rgx.Compile(false, false));
                    var rgxTime = sw.Elapsed.TotalMilliseconds;
                    t += rgxTime;
                    if (version == Version.CHIPMUNK || version == Version.BOTH)
                    {

                        sw.Restart();
                        // change according to monadic-nonmonadic
                        nca = pattern.Pattern.CreateCountingAutomatonPushIncr(false);
                        ncaTime = sw.Elapsed.TotalMilliseconds;                        
                        sw.Restart();
                        dca = nca.CompileOpt(1);
                        var dcaTime = sw.Elapsed.TotalMilliseconds;
                        t += dcaTime;                       
                    }
                }
                catch (Exception e)
                {
                    if (e.InnerException != null)
                    {
                        Console.WriteLine(e.InnerException.Message);
                        Console.WriteLine("Some weird error.");
                    }
                    else // timeout
                    {
                        Console.WriteLine(e.Message);
                        Console.WriteLine(e.StackTrace);

                        Console.WriteLine(e.Source);
                        System.Diagnostics.Trace.TraceError(e.StackTrace);
                        Console.WriteLine("Timeout error.");
                    }
                }
            }

            //CSMatcher matcher = null;
            //matcher = new CSMatcher();
             double t1 = 0;
             double t2 = 0;
             int countMatch1 = 0;
             int countMatch2 = 0;
            int h = 0;
            int ms = 0;
            List<string> tab1 = new List<string>();
            List<string> tab2 = new List<string>();

            foreach (var str in text)
            {
                if (version == Version.CHIPMUNK || version == Version.BOTH)
                {
                    sw.Restart();

                    if (pattern.IsMatchCA(str, dca, false))
                    {
                        countMatch1++;
                        countMatch++;
                        tab1.Add(str);
                        //Console.WriteLine(str);
                        //Console.WriteLine("Hits: " + matcher.hit);
                        //Console.WriteLine("Miss: " + matcher.miss+ "\n");
                    }
                    var timeMatch = sw.Elapsed.TotalMilliseconds;
                    t1 += timeMatch;
                    t += timeMatch;

                    /* sw.Restart();
                     if (pattern.IsMatchCA(str, dca, matcher, true))
                     {
                         countMatch++;
                         //Console.WriteLine(str);
                         //Console.WriteLine("Hits: " + matcher.hit);
                         //Console.WriteLine("Miss: " + matcher.miss+ "\n");
                     }
                     timeMatch = sw.Elapsed.TotalMilliseconds;
                     t2 += timeMatch;*/
                }
                if(version == Version.MARGUS || version == Version.BOTH)
                {
                    sw.Restart();
                    int misses = 0;
                    int hits = 0;
                    if (pattern.IsMatch(str, out misses, out hits))
                    {
                        countMatch2++;
                        countMatch++;
                        tab2.Add(str);
                        //Console.WriteLine(str);
                    }
                    //ms += misses;
                    //h += hits;
                    var timeMatch = sw.Elapsed.TotalMilliseconds;
                    t += timeMatch;
                   t2 += timeMatch;

                }
                if(version == Version.REGEX)
                {
                    sw.Restart();
                    var m = rgx.Match(str);
                    if (m.Success)
                    {
                        countMatch++;
                        //Console.WriteLine(str);
                    }
                    var timeMatch = sw.Elapsed.TotalMilliseconds;
                    t += timeMatch;
                }
            }

            /*            Console.WriteLine("No-caching: " + t1 + "\n");
                        Console.WriteLine("Caching: " + t2 + "\n");
                        Console.WriteLine("Hits: " + matcher.hit);
                        Console.WriteLine("Miss: " + matcher.miss+ "\n");*/
           /* Console.WriteLine("Hits: " + h );
            Console.WriteLine("Misses: " + ms);*/
            if(version == Version.BOTH)
            {
                Console.WriteLine("Chipmunk: " + t1 + "[ms]");
                Console.WriteLine(" " + countMatch1 + " lines");
                Console.WriteLine("SRM:      " + t2 + "[ms]");
                Console.WriteLine(" " + countMatch2 + " lines \n");
                double o = (int)(t1 / t2);
                if(o > 0)
                    Console.WriteLine("It is " + o + " times slower.\n");
                else
                {
                    double oo = (int)(t2 / t1);
                   Console.WriteLine("It is " + oo + " times faster.\n");

                }
                Console.Write("missing:\n");
                foreach (var str in tab2)
                {
                    if (!tab1.Contains(str))
                        Console.WriteLine(str);
                }
                Console.Write('\n');
                Console.Write("extra lines:\n");
                foreach (var str in tab1)
                {
                    if (!tab2.Contains(str))
                        Console.WriteLine(str);
                }
                /* foreach (var str in tab1)
                 {
                     Console.WriteLine(str);
                 }*/
            }
             
            time = t;
            count = countMatch;
            // stats postprocessing
            return stats;
        }        

        // Replace curly brackets and double backslashes
        static string Decode(string input)
        {
            string pattern = @"((\{)([0-9]*)([0-9]{4})(\}))";
            input = Regex.Replace(input, pattern, "$4");

            var output = new System.Text.StringBuilder();
            int r0 = 0; int r1 = 0; int r2 = 0; int r3 = 0; int r4 = 0; int r5 = 0; int state = 0;
            var chars = input.ToCharArray();
            for (int i = 0; i < chars.Length; i++)
            {
                int c = (int)chars[i];
                switch (state)
                {
                    case (0):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append((char)c);
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (1):
                        {
                            switch (c)
                            {
                                case (0x78):
                                    {
                                        state = 2;
                                        break;
                                    }
                                case (0x75):
                                    {
                                        state = 3;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append((char)0x5C);
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (3):
                        {
                            switch (c)
                            {
                                case (0x7B):
                                    {
                                        state = 4;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (4):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r0 = c;
                                            state = 5;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (5):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x30, (char)0x30, (char)0x30, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r1 = c;
                                            state = 6;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (6):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x30, (char)0x30, (char)r0, (char)r1 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r2 = c;
                                            state = 7;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (7):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x30, (char)r0, (char)r1, (char)r2 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r3 = c;
                                            state = 8;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (8):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)r0, (char)r1, (char)r2, (char)r3 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r4 = c;
                                            state = 9;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (9):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)r1, (char)r2, (char)r3, (char)r4 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r5 = c;
                                            state = 10;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (10):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)r2, (char)r3, (char)r4, (char)r5 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (2):
                        {
                            switch (c)
                            {
                                case (0x5B):
                                    {
                                        state = 11;
                                        break;
                                    }
                                case (0x7B):
                                    {
                                        state = 12;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (12):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r0 = c;
                                            state = 13;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (13):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x30, (char)0x30, (char)0x30, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r1 = c;
                                            state = 14;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (14):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x30, (char)0x30, (char)r0, (char)r1 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r2 = c;
                                            state = 15;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (15):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x30, (char)r0, (char)r1, (char)r2 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r3 = c;
                                            state = 16;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (16):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)r0, (char)r1, (char)r2, (char)r3 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r4 = c;
                                            state = 17;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (17):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)r1, (char)r2, (char)r3, (char)r4 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        if ((((0x30 <= c) && (((c >> 6) & 0x3FF) == 0) && ((c & 0x3F) <= 0x39)) || ((0x41 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x46)) || ((0x61 <= c) && (((c >> 7) & 0x1FF) == 0) && ((c & 0x7F) <= 0x66))))
                                        {
                                            r5 = c;
                                            state = 18;
                                        }
                                        else
                                        {
                                            output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)c });
                                            r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                            state = 0;
                                        }
                                        break;
                                    }
                            }
                            break;
                        }
                    case (18):
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x7D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)r2, (char)r3, (char)r4, (char)r5 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (11):
                        {
                            switch (c)
                            {
                                case (0x30):
                                    {
                                        r0 = 0x30;
                                        state = 19;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (19):
                        {
                            switch (c)
                            {
                                case (0x2D):
                                    {
                                        r1 = 0x2D;
                                        state = 20;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (20):
                        {
                            switch (c)
                            {
                                case (0x39):
                                    {
                                        r2 = 0x39;
                                        state = 21;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (21):
                        {
                            switch (c)
                            {
                                case (0x41):
                                    {
                                        r3 = 0x41;
                                        state = 22;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (22):
                        {
                            switch (c)
                            {
                                case (0x2D):
                                    {
                                        r4 = 0x2D;
                                        state = 23;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (23):
                        {
                            switch (c)
                            {
                                case (0x46):
                                    {
                                        r5 = 0x46;
                                        state = 24;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (24):
                        {
                            switch (c)
                            {
                                case (0x61):
                                    {
                                        state = 25;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (25):
                        {
                            switch (c)
                            {
                                case (0x2D):
                                    {
                                        state = 26;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    case (26):
                        {
                            switch (c)
                            {
                                case (0x66):
                                    {
                                        state = 27;
                                        break;
                                    }
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                    default:
                        {
                            switch (c)
                            {
                                case (0x5C):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D, (char)0x66 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 1;
                                        break;
                                    }
                                case (0x5D):
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x30, (char)0x30, (char)0x30, (char)r0 });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                                default:
                                    {
                                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D, (char)0x66, (char)c });
                                        r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0; r5 = 0;
                                        state = 0;
                                        break;
                                    }
                            }
                            break;
                        }
                }
            }
            switch (state)
            {
                case (0):
                    {
                        break;
                    }
                case (1):
                    {
                        output.Append((char)0x5C);
                        break;
                    }
                case (3):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75 });
                        break;
                    }
                case (4):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B });
                        break;
                    }
                case (5):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0 });
                        break;
                    }
                case (6):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1 });
                        break;
                    }
                case (7):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2 });
                        break;
                    }
                case (8):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3 });
                        break;
                    }
                case (9):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                        break;
                    }
                case (10):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x75, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                        break;
                    }
                case (2):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78 });
                        break;
                    }
                case (12):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B });
                        break;
                    }
                case (13):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0 });
                        break;
                    }
                case (14):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1 });
                        break;
                    }
                case (15):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2 });
                        break;
                    }
                case (16):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3 });
                        break;
                    }
                case (17):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                        break;
                    }
                case (18):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x7B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                        break;
                    }
                case (11):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B });
                        break;
                    }
                case (19):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0 });
                        break;
                    }
                case (20):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1 });
                        break;
                    }
                case (21):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2 });
                        break;
                    }
                case (22):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3 });
                        break;
                    }
                case (23):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4 });
                        break;
                    }
                case (24):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5 });
                        break;
                    }
                case (25):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61 });
                        break;
                    }
                case (26):
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D });
                        break;
                    }
                default:
                    {
                        output.Append(new char[] { (char)0x5C, (char)0x78, (char)0x5B, (char)r0, (char)r1, (char)r2, (char)r3, (char)r4, (char)r5, (char)0x61, (char)0x2D, (char)0x66 });
                        break;
                    }
            }

            string str = output.ToString();
            try
            {
                str = ReplaceSubstrings(Regex.Unescape(str));
            }
            catch
            {
                Console.WriteLine("Error in substring replacement.");
                return ReplaceSubstrings(str);
            }
            return ReplaceSubstrings(str);
        }

        static string ReplaceSubstrings(string str)
        {
            str = str.Replace("\\Q", "q");
            str = str.Replace("\\E", "e");
            str = str.Replace("\\G", "g");
            str = str.Replace("\\A", "^");
            str = str.Replace("\\Z", "$");
            str = str.Replace("\\z", "$");
            str = str.Replace("\\K", "K");
            str = str.Replace("\\k", "k");
            str = str.Replace("\\b", "b");
            str = str.Replace("\\B", "b");
            str = str.Replace("\\N", "n");
            str = str.Replace("\\e", "e");
            str = str.Replace("\\cc", "c");
            str = str.Replace("\\cC", "c");
            str = str.Replace("\\s", "s");
            str = str.Replace("\\_", ".*");
            str = str.Replace("\\g", "escapeG");
            str = Regex.Replace(str, "escapeG\\<[+-]*[0-9a-zA-Z]+\\>", "g");
            str = Regex.Replace(str, "escapeG\\{[+-]*[0-9a-zA-Z]+\\}", "g");
            str = Regex.Replace(str, "escapeG[0-9a-zA-Z]+", " g");
            str = str.Replace("\\p", "escapeP");
            str = Regex.Replace(str, "escapeP\\{[+-]*[0-9a-zA-Z]+\\}", "p");
            str = Regex.Replace(str, "escapeP[a-zA-Z]", " p");
            str = str.Replace("[:alpha:]", "[A-Za-z]");
            str = str.Replace("[:upper:]", "[A-Z]");
            str = str.Replace("[:lower:]", "[a-z]");
            str = str.Replace("[:digit:]", "[0-9]");
            str = str.Replace("[:alnum:]", "[A-Za-z0-9]");
            str = str.Replace("[:xdigit:]", "[A-Fa-f0-9]");
            str = str.Replace("[:space:]", "[ \t\r\n\v\f]");
            str = str.Replace("[:black:]", "[ \t]");
            str = str.Replace("[:print:]", "[\x20-\x7E]");
            str = str.Replace("[:punct:]", "[\\p{P}]");
            str = str.Replace("[:graph:]", "[\x21-\x7E]");
            str = str.Replace("[:word:]", "[A-Za-z0-9_]");
            str = str.Replace("[:ascii:]", "[\x00-\x7F]");
            str = str.Replace("[:cntrl:]", "[\x00-\x1F\x7F]");
            str = str.Replace("\\h", "h");
            str = str.Replace("\\H", "H");
            str = str.Replace("\\R", "R");
            str = str.Replace("\\d", "d");
            str = str.Replace("\\V", "V");
            str = str.Replace("\\C", "C");
            str = str.Replace("\\T", "T");
            str = str.Replace("\\i", "i");
            str = str.Replace("\\x[", "x[");
            str = str.Replace("\\u[", "u[");
            str = str.Replace("|*", "|.*");
            str = str.Replace("+?", "+");
            str = str.Replace("?+", "+");
            str = str.Replace("??", "?");
            str = str.Replace("?*", "*");
            str = str.Replace("++", "+");
            str = str.Replace("}?", "}");
            str = str.Replace("}+", "}");
            str = str.Replace("}*", "}");
            str = str.Replace("+{", "{");
            str = str.Replace("*{", "{");
            str = str.Replace("?{", "{");
            str = str.Replace("*?", "*");
            str = str.Replace("+*", "+");
            str = str.Replace("*+", "*");
            str = str.Replace("|?", "|.*");
            str = str.Replace("{ ", "{");
            str = str.Replace(" }", "}");
            str = str.Replace("{}", ".*");
            str = str.Substring(0, str.Length - 1).Replace("$", ".*") + str.Substring(str.Length - 1);

            //string pattern = @"(\(\?[\>\=\!]*)(.*?)(\))";
            //str = Regex.Replace(str, pattern, "$2");

            // (?xus)"  (?<=a(?=([bc]{2}(?<!a{2}))d)\\w{3})\\w\\w

            string pattern = @"(\(\?([^\)]+)\))";
            string oldStr = "";
            while (oldStr != str)
            {
                oldStr = str;
                str = Regex.Replace(str, pattern, "($2)");
            }
            str = str.Replace("(?)", "(.*)");

            // *compute tau *
            pattern = @"((\*)([^\*]*)(\*))";
            str = Regex.Replace(str, pattern, "$3");

            // {HAN}
            pattern = @"((\{)([^\}[0-9]]*)(\}))";
            str = Regex.Replace(str, pattern, "$3");
            
            // {1}{2}
            pattern = @"((\{[0-9,]+\})(\{[0-9,]+\}))*";
            str = Regex.Replace(str, pattern, "$2");

            // ?(3)
            str = Regex.Replace(str, "(\\?\\()([0-9]?)(\\))", ".*");

            // \1
            pattern = @"(\\)([0-9]+)";
            str = Regex.Replace(str, pattern, "$2");
            
            return str;
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
            return (!m.Pattern.ExistsNode(isNonMonadic)) ;
        }

        static string[] FilterRegexes(string[] regexes, out List<string> notSupported, out List<string> nonMonadic, out List<string> noCounters, out List<string> simpleStrings, out List<string> nestedCounters, out List<string> notnestedCounters, bool banchmark_mode = false, bool filter_mode = true, bool decode_mode = false)
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
        }

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
        static void BenchmarkFile(string[] args, Version version)
        {
            var regex = args[1];
            List<string> text = new List<string>();
            if (args.Length == 3)
                text = ReadText(args[2]).ToList();
            string filenameNoExtension = "regex-" + Guid.NewGuid();
            double time = 0;
            int count = 0;
            var stats = Benchmark(regex, text, out time, out count, version);
            if (version != Version.BOTH)
                Console.WriteLine("Time: " + time.ToString() + " ms");
            if(args.Length == 3)
            {

                if (text.Count == 0)
                    Console.WriteLine("Input file is empty.");
                else if(version != Version.BOTH)
                {
                    Console.WriteLine("Matching lines: "+ count);
                    //Console.WriteLine("");
                }
            }
        }

        static void Main(string[] args)
        {
            if (args.Length < 1 || args.Length > 3)
            {
                Console.Error.WriteLine("Usage: CounterAutomataBench.exe --[margus|chipmunk|both|regex] <regex> [<matching-file>]\n--margus : SRM\n--chipmunk : our algorithm \n--both : both SRM and our\n--regex : .NET \n ");
                //System.Environment.Exit(1);
                Console.ReadLine();
                return;
            }
            var version = Version.CHIPMUNK;
            if (args[0] == "--margus")
                version = Version.MARGUS;
            else if (args[0] == "--chipmunk")
                version = Version.CHIPMUNK;
            else if (args[0] == "--regex")
                version = Version.REGEX;
            else if (args[0] == "--both")
                version = Version.BOTH;
            else
            {
                Console.Error.WriteLine("Usage: CounterAutomataBench.exe --[margus|chipmunk|both|regex] <regex> [<matching-file>]\n--margus : SRM\n--chipmunk : our algorithm \n--both : both SRM and our\n--regex : .NET \n ");
                //System.Environment.Exit(1);
                Console.ReadLine();
                return;
            }
            BenchmarkFile(args, version);

          Console.ReadLine();
        }
    }
}
