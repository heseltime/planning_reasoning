import os
import sys

if len(sys.argv) < 2:
    sys.exit('Usage: %s <problem size>' % sys.argv[0])

def nl(f):
    f.write('\n')

# Output file
filename = '%squeensGenerated.smt2' % sys.argv[1]
f = open(filename, 'w')

N = int(sys.argv[1])
print("Opening %s to write the SMT-LIB v2 encoding of the %i-queens problem" % (filename, N))

f.write(';; Generate the definitions of the variables\n')
for i in range(0, N):
    for j in range(0,N):
        f.write('(declare-const x%iy%i Bool)\n' % (i, j))

f.write(';;Generate the "one queen by line" clauses\n\n')
for i in range(0,N):
    f.write('(assert (or')
    for j in range(0, N-1):
        f.write(' x%iy%i ' % (i,j))
    f.write('x%iy%i' %(i, N-1))
    f.write('))')
    f.write('\n')


f.write('\n;;Generate the "only one queen by line" clauses\n\n')
for i in range(0,N):
    f.write('(assert (not (or')
    for j in range(1, N):
        for k in range(0,j):
            f.write('(and x%iy%i x%iy%i)' %(i,j,i,k))
    f.write(')))')
    nl(f)
nl(f)

f.write(';;Generate the "only one queen by column" clauses\n')
for i in range(0,N):
    f.write('(assert (not (or')
    for j in range(1, N):
        for k in range(0,j):
            f.write('(and x%iy%i x%iy%i)' %(j,i,k,i))

    f.write(')))')
    nl(f)
nl(f)

f.write(';;Generate the "only one queen by diagonal" clauses\n')
for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(j,i+j,j+k,i+j+k))
    f.write(')))')
    nl(f)

for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(i+j,j,i+j+k,j+k))
    f.write(')))')
    nl(f)

for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(j+k,i+j+k,j,i+j))
    f.write(')))')
    nl(f)

for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(i+j+k,j+k,i+j,j))
    f.write(')))')
    nl(f)

nl(f)


f.write(";; Check if the generate model is satisfiable and output a model.\n")
f.write("(check-sat)\n")
f.write("(get-model)\n")
f.close()

# solution_filename = 's%i_queens.txt' %  N
# os.system('z3 %s > %s' % (filename, solution_filename))
# solution_file = open(solution_filename, 'r')