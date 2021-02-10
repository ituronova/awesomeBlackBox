File: README.TXT
Author: Lenka Turoňová

./Experiments
- main project for testing regexes

tests.TestCountingSetAutomataMatch()
- converte regexs into DCA and try to find matches

var regex = new Regex("[a-z0-9/\\+]{44}", RegexOptions.Singleline);
- set regular expression
var sr = (SymbolicRegex<ulong>)regex.Compile(false, false);
- compile regular expression into symbolic regular expression tree

sr.Pattern - regular expression
sr.Atoms   - bit numbers for each minterm

RegexTree rt = RegexParser.Parse(regex.ToString(), regex.Options);
- parse regexes
- regex - regular expression
- regex.Options - mode of regular expression, usually Singleline

// Single-line summary:
//     Specifies single-line mode. Changes the meaning of the dot (.) so it matches
//     every character (instead of every character except \n). For more information,
//     see the "Single-line Mode" section in the Regular Expression Options topic.

NOTE: some function that might be interesting for parsing (Experiments/Compile/Parse):
- CountCaptures(); 
- ScanRegex();

(Experiments/Compile/Parse) public S[] ComputeMinterms()
- compute minterms
- GetPredicate - all predicate in the reges
- EnumerateMinterms() - compute from predicate minterms




[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			4
[probShuffle]		0
[probGenPattern]	100
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			4
[probShuffle]		0
[probGenPattern]	100
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

[inputFile]			C:\Users\42073\Desktop\Code\Automata\test.txt
[outputFolder]		C:\Users\42073\Desktop\Code\Automata
[TIMEOUT]			600000
[TIMEOUTGen]		24000
[lines]				200
[maxLine]			100
[probCut]			0
[probShuffle]		0
[probGenPattern]	0
[-f|-nf]	-f

