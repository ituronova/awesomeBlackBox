using Microsoft.Automata;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Globalization;
using System.Text;
using System.Threading.Tasks;
using System.Timers;
using System.Threading;

namespace CounterAutomataBench
{
   class Program
    {
        static long LongRandom(long min, long max, Random rand)
        {
            byte[] buf = new byte[8];
            rand.NextBytes(buf);
            long longRand = BitConverter.ToInt64(buf, 0);
            return (Math.Abs(longRand % (max - min)) + min);
        }

        private static bool graphs;
        private static string inputFile;
        private static string outputFolder;
        private static int bound;
        private static bool verbose;
        private static errCode cntE;
        private static bool hybrid;
        private static int done = 0;
        private static int timeouted = 0;
        private static int error = 0;
        private static int index = 0;
        private static string n = "";
        private static CsAutomatonOpt<ulong> dca = null;
        private static string outputRegex = "";
        private static int count;
        private static string s = String.Empty;
        private static Regex rgx = null;
        private static SymbolicRegex<ulong> sRegex = null;
        private static string name;
        private static string timeFile;
        private static double ncaTime;
        private static double dcaTime;
        private static double genTime;
        private static double weightTime;
        private static string errorFile;
        private static string errorRegex;
        private static double time;
        private static string message;
        private static CountingAutomaton<ulong> nca = null;
        private static string output;
        private static string read;
        private static Stopwatch sw;
        private static string outputFile;


        public enum errCode
        {
            ok = 0,
            gen = 1,
            dca = 2,
            weight = 3,
        }
        private static void LongRunningMethod()
        {
            try
            {
                index++;
                n = outputRegex + "_" + index + ".txt";
                if (s == string.Empty)
                        return;
                
                count++;
                cntE = errCode.ok;
                dca = null;
                rgx = null;
                sRegex = null;
                nca = null;
                // convert regex to DCA
                sw.Restart();
                rgx = new Regex(s, RegexOptions.Singleline);

               // sRegex = ((SymbolicRegex<ulong>)rgx.Compile(false, true, "[\t\n\r\x20-\x7F]"));
               //sRegex = ((SymbolicRegex<ulong>)rgx.Compile(false, true, "[\t\n\r\x20]"));
                sRegex = ((SymbolicRegex<ulong>)rgx.Compile(false,false));
                // create NCA
                nca = sRegex.Pattern.CreateCountingAutomatonPushIncr(false);
                // nca.ShowGraph("nca-f");
              
                ncaTime = sw.ElapsedMilliseconds;
                Console.WriteLine("NCA: " + ncaTime);
                sw.Restart();
                if (graphs)
                {
                    Microsoft.Automata.DirectedGraphs.Options.MaxDgmlTransitionLabelLength = 1000000;
                    nca.ShowGraph("NCA - chart" + index, true);
                }
                dca = nca.CompileOpt(1, true);
                dcaTime = sw.ElapsedMilliseconds;
                Console.WriteLine("DCA: " + dcaTime);
                if (graphs)
                {
                    dca.ShowGraph("DCA - chart" + index, true);
                }                
            }
            catch (Exception e)
            {
                if (!e.Message.Contains("Thread"))
                { 
                    Console.WriteLine("Error while converting regex to DCA: " + e.Message + "\n");
                    error++;
                    message = e.Message + "\n";
                    cntE = errCode.dca;
                }
                return;
            }
            //Console.WriteLine("DCA states: " + dca.cntStates.ToString());
            // hybrid version compute weight
            if (hybrid)
            {
                try
                {
                    sw.Restart();
                    dca.Preprocessing(rgx.ToString());
                    dca.WeightCycles(verbose);
                    if (verbose)
                    {
                        Console.WriteLine("Find cycles finished.");
                    }
                    dca.SpreadWeight(verbose);
                    weightTime = sw.ElapsedMilliseconds;
                    Console.WriteLine("Weight cycles and spread weight: " + weightTime);

                    if (verbose)
                    {
                        Console.WriteLine("Add cycles finished.");
                        if (graphs)
                        {
                            dca.ShowGraph("dca-weight", true);
                        }
                    }
                }
                catch (Exception e)
                {
                    if (!e.Message.Contains("Thread"))
                    {
                        Console.WriteLine("Error while finding cycles: " + e.Message);
                        error++;
                        message = e.Message + "\n";
                        cntE = errCode.dca;
                    }
                    return;
                    
                }
            }
            try
            {
                dca.InitConfAut();
                sw.Restart();
                dca.GenerateRandomText(bound, verbose, outputFolder, n, hybrid);
                genTime = sw.ElapsedMilliseconds;
                Console.WriteLine("Generate text: " + genTime);

           }
            catch (Exception e)
            {
                if(!e.Message.Contains("Thread"))
                {
                    Console.WriteLine("Error while generating text: " + e.Message + "\n");
                    error++;
                    message = e.Message + "\n";
                    cntE = errCode.gen;
                }
               
                if (verbose)
                {
                    dca.dotFile += "}";
                    using (var sv = new StreamWriter(outputFolder + "/dotGraph_" + LongRandom(100000, 100050, new Random()) + ".dot", true))
                    {
                        sv.WriteLine(dca.dotFile);
                    }
                }
              
                return;                
            }
            done++;
            return;            
        }

        static bool RunWithTimeout(ThreadStart threadStart, TimeSpan timeout)
        {
            

            Thread workerThread = new Thread(threadStart);

            workerThread.Start();

            bool finished = workerThread.Join(timeout);
            if (!finished)
                workerThread.Abort();

            return finished;
        }

        static void Main(string[] args)
        {
            
            sw = new Stopwatch();

            //graphs = true;
            graphs = false;
            if (args.Length < 6)
            {
                Console.WriteLine("\n---------------------------  HELP --------------------------\n");
                Console.WriteLine("Usage: ./CounterAutomataBench [inputFile] [outputFolder] [bound] [TIMEOUT] [-v/-nv] [-hybrid/-nonhybrid]\n");
                Console.WriteLine("\n-------------------------------------------------------------\n");
                Console.Read();
                return;
            }
            inputFile = args[0];
            outputFolder = args[1];
           // bound = Int32.Parse(args[2]);
            int TIMEOUT = Int32.Parse(args[2]);
            verbose = false;
            cntE = errCode.ok;
            hybrid = false;
            done = 0;
            timeouted = 0;
            error = 0;

            if (args[5].Contains("-hybrid"))
            {
                hybrid = true;
            }

            if (args[4].Contains("-v"))
            {
                verbose = true;
                Console.WriteLine("\n---------------------------  HELP --------------------------\n");
                Console.WriteLine("Usage: ./CounterAutomataBench [inputFile] [outputFolder] [TIMEOUT]\n");
                Console.WriteLine("Input file:\t" + inputFile);
                Console.WriteLine("Output folder:\t" + outputFolder);
              //  Console.WriteLine("Bound for visited:\t" + bound);
                Console.WriteLine("TIMEOUT:\t" + TIMEOUT); 
                //Console.WriteLine("Verbose:\ttrue");
                //Console.WriteLine("Hybrid:\t\ttrue");
                Console.WriteLine("\n-------------------------------------------------------------\n");
            }
       /*     System.IO.Directory.CreateDirectory("./results/results-" + DateTime.Now.ToString("yyyy-MM-dd") + "/");
            System.IO.Directory.CreateDirectory(outputFolder);

            output = "./results/results-" + DateTime.Now.ToString("yyyy-MM-dd") + "/";
            read = "Input file:\t" + inputFile + "\n";
            read += "Output folder:\t" + outputFolder + "\n";
            read += "Bound for visited:\t" + bound + "\n";
            read += "TIMEOUT:\t" + TIMEOUT + "\n*/

          //  name = Path.GetFileNameWithoutExtension(inputFile);
            //timeFile = output + name + "-timeout.txt";
            //errorFile = output + name + "-error.csv";
            //errorRegex = output + name + "-error.txt";
            //string readme = output + "README.txt";
            //File.AppendAllText(errorFile, "Pattern;Message;\n");
            //File.AppendAllText(readme, read);

          //  string ofAna = output + "analysis.csv";
            //outputFile = output + "genText-" + Path.GetFileNameWithoutExtension(inputFile) + "-" + LongRandom(100000, 100050, new Random()) + ".csv";
           // outputRegex = outputFolder + "/" + Path.GetFileNameWithoutExtension(inputFile);
         //   File.AppendAllText(outputFile, "Regex;Lines;Visited;Cache Size(Found);Counters;Max Counter;Sum Counters;Max CS;Avrg CS;DCA-states;DCA-trans;NCA-time[ms];DCA-time[ms];Weight-time[ms];Gen-time[ms];Time[ms];Status\n");

            index = 0;
            n = "";
            // read input parameters to variables
            dca = null;
            time = 0;
            count = 0;
            Stopwatch swAll = new Stopwatch();

            hybrid = true;
            //s1.Reset();
            using (StreamReader sr = File.OpenText(inputFile))
            {
                s = String.Empty;
                while ((s = sr.ReadLine()) != null)
                {
                    // initialization
                    dca = null;
                    rgx = null;
                    sRegex = null;
                    nca = null;
                    // timers
                    ncaTime = 0;
                    dcaTime = 0;
                    genTime = 0;
                    weightTime = 0;
                    verbose = false;
                    swAll.Restart();
                    Console.WriteLine(s);
                    if (!RunWithTimeout(LongRunningMethod, TimeSpan.FromMilliseconds(TIMEOUT)))
                    {
                        
                        time = ncaTime + dcaTime + weightTime + genTime;
                        timeouted++;
                    //    File.AppendAllText(timeFile, s + "\n");
                        if (dca == null)
                        {
                            if (sRegex == null)
                                Console.WriteLine("TIMEOUT while compiling regex.\n");
                            //File.AppendAllText(outputFile, s + ";;;;;;;;;;;;;;;;TIMEOUT REGEX.\n");
                            else if (nca == null)
                                Console.WriteLine("TIMEOUT while converting to NCA.\n");
                            //File.AppendAllText(outputFile, s + ";;;;;;;;;;;;;;;;TIMEOUT NCA.\n");
                            else if (dca == null)
                                Console.WriteLine("TIMEOUT while converting to DCA.\n");
                            // File.AppendAllText(outputFile, s + ";" + " " + ";" + " " + ";;" + " " + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";;;" + " " + ";" + " " + ";" + ncaTime.ToString() + ";" + " " + ";" + " " + ";" + " " + ";" + " " + ";TIMEOUT DCA.\n");
                            else
                                Console.WriteLine("TIMEOUT while computing weight.\n");
                            // File.AppendAllText(outputFile, s + ";;;;" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";0;0;" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString() + ";;;;TIMEOUT WHILE COMPUTING WEIGHT.\n");
                        }
                        else if (dca.sizeCA == null)
                        {
                           /* if (verbose)
                            {
                                dca.dotFile += "}";
                                using (var sv = new StreamWriter(outputFolder + "/dotGraph_" + LongRandom(100000, 100050, new Random()) + ".dot", true))
                                {
                                    sv.WriteLine(dca.dotFile);
                                }
                            }*/
                            Console.WriteLine("TIMEOUT while spreading weight.\n");
                           // File.AppendAllText(outputFile, s + ";;;;" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";;;" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString()+ ";"+ weightTime + ";" + genTime.ToString() + ";;TIMEOUT SPREAD WEIGHT OR BEFORE GEN TEXT.\n");
                        }
                        else
                        {
                            //var fileN = outputFolder  +"\\"+  name + n;
                            //File.AppendAllText(fileN, dca.str + "\n");
                            //File.AppendAllText(outputFile, s + ";;;;" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";;;" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString() + ";" + weightTime + ";;;TIMEOUT GEN TEXT.\n");
                            //File.AppendAllText(n, dca.str + "\n");
                            if(dca.str.Length == 0)
                                Console.WriteLine("Timeout generating text.\n");
                            else
                                Console.WriteLine("File generated (TIMEOUT while generating text).\n");
                        }
                    }
                    else
                    {
                        time = ncaTime + dcaTime + weightTime + genTime;
                        switch (cntE)
                        {
                            case errCode.ok:
                                //Console.WriteLine("File generated\n");
                                break;
                            case errCode.dca:
                                Console.WriteLine("ERROR WHILE CONVERTING TO DCA.\n");
                                break;
                            case errCode.weight:
                                Console.WriteLine("Error while spreading weight.\n");
                                break;
                            case errCode.gen:
                                Console.WriteLine("Error while generating text.\n");
                                break;
                        }
                        /* switch (cntE)
                         {
                             case errCode.ok:
                                 File.AppendAllText(n, dca.str + "\n");
                                 File.AppendAllText(outputFile, s + ";" + dca.line + ";" + dca.visited + ";" + dca.mapConf.Count() + ";" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";" + dca.sizeCA.Max() + ";" + dca.sizeCA.Average() + ";" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString() + ";" + weightTime.ToString() + ";" + genTime.ToString() + ";" + time + ";DONE.\n");
                                 break;
                             case errCode.dca:
                                 File.AppendAllText(errorFile, s + ";" + message + "\n");
                                 File.AppendAllText(errorRegex, s + "\n");
                                 File.AppendAllText(outputFile, s + ";ERROR WHILE CONVERTING TO DCA.\n");
                                 break;
                             case errCode.weight:
                                 File.AppendAllText(errorFile, s + ";" + message + "\n");
                                 File.AppendAllText(errorRegex, s + "\n");
                                 File.AppendAllText(outputFile, s + ";ERROR WHILE FINDING CYCLES.\n");
                                 File.AppendAllText(outputFile, s + ";;;;" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";;;" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString() + ";;;;ERROR WHILE WEIGHTING CYCLES.\n");
                                 break;
                             case errCode.gen:
                                 File.AppendAllText(errorFile, s + ";" + message + "\n");
                                 File.AppendAllText(errorRegex, s + "\n");
                                 File.AppendAllText(n, dca.str + "\n");
                                 File.AppendAllText(outputFile, s + ";;;;" + dca.cntCount + ";" + nca.MaxCounter() + ";" + nca.MaxSumCounter() + ";;;" + dca.cntStates + ";" + dca.CountTrans() + ";" + ncaTime.ToString() + ";" + dcaTime.ToString() + ";" + weightTime.ToString() + ";;;ERROR WHILE GENERATING TEXT.\n");
                                 break;
                         }
                       */
                    }
                }              
              }
            // File.AppendAllText(ofAna, "Benchmark;Suma;Done;Errors;Timeouted;\n");
            //File.AppendAllText(ofAna, Path.GetFileNameWithoutExtension(inputFile) + ";" + count+ ";" +done + ";" + error+ ";" + timeouted + ";\n", Encoding.UTF8);
              //Console.WriteLine(name + " done....\n");

           // Console.Write("Press ENTER...");
           /// Console.Read();
          }
    }
}
