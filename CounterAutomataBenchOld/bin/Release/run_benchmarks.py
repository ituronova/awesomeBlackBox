import glob
import csv
import sys
import os
import subprocess

def read_file(path):
    with open(path, 'r') as f:
        return f.read().split('\n')


    
file_content = read_file("C:\\Users\\42073\\Desktop\\Code\\Automata\\regexes\\test-simple.txt")

for regex in file_content:
   cmd = "./CounterAutomataBench --both \"" + regex + "\" \"C:\\Users\\42073\\Desktop\\Code\\Automata\\pg3200.txt\""
   #os.system(cmd)
   #print(cmd)
   process = subprocess.Popen(cmd)#.split(), stdout=subprocess.PIPE)
   print("\n")
   output, error = process.communicate()
   #print(both)
   #if(output != None):
    #   print(output)
   #if(error != None):
    #   print(error)
    

#with open('results\\excel\\summary.csv', 'wb') as f:
#	writer = csv.writer(f, delimiter=';')
#	writer.writerow(["Benchmark", "Regexes", "NCA-states", "NCA-trans", "DCA-states", "DCA-trans", "Our time", "Our timeouts", "DFA-states", "DFA-trans", "Classical time", "Classical timouts", "States-comparison", "Trans-comparison", "Time-comparison" ])
#	for row in table_rows:
#		writer.writerow(row)
