import os
import sys

# 2023-12, Planning and Reasoning Project
# Sarah and Jack

# Code to generate the SMT2 encoding of the N-Queens problem for a given N

if len(sys.argv) < 2:
    sys.exit('Usage: %s <problem size>' % sys.argv[0])

def nl(f):
    f.write('\n')

filename = '%squeensGenerated.smt2' % sys.argv[1]
f = open(filename, 'w')

N = int(sys.argv[1])
print('Writing SMT2 encoding of the %i-queens problem to  %s ...' % (N, filename))

f.write('; 2023-12, Planning and Reasoning Project - Generated Code! See generate.py \n')
f.write('; Sarah and Jack\n')
f.write(';\n')
f.write('; N-queens problem for the %d x %d case to start, see comments above code blocks for approach (SMT2)\n' % (N,N))
f.write(';\n')
f.write('; see https://jfmc.github.io/z3-play/ for a current (2023-12) z3 web interface to execute\n')

nl(f)

f.write('; playing field\n')
for i in range(0, N):
    for j in range(0,N):
        f.write('(declare-const x%iy%i Bool)\n' % (i, j))

nl(f)

f.write('; %i queens on the field, one per row\n' % N)
for i in range(0,N):
    f.write('(assert (or')
    for j in range(0, N-1):
        f.write(' x%iy%i ' % (i,j))
    f.write('x%iy%i' %(i, N-1))
    f.write('))')
    f.write('\n')

nl(f)

f.write('; 2 queens should never be on the same line ...\n')
for i in range(0,N):
    f.write('(assert (not (or')
    for j in range(1, N):
        for k in range(0,j):
            f.write('(and x%iy%i x%iy%i)' %(i,j,i,k))
    f.write(')))')
    nl(f)

nl(f)

f.write('; ... or column ...\n')
for i in range(0,N):
    f.write('(assert (not (or')
    for j in range(1, N):
        for k in range(0,j):
            f.write('(and x%iy%i x%iy%i)' %(j,i,k,i))

    f.write(')))')
    nl(f)

nl(f)

f.write('; ... or diagonal: both directions! We start with the main diagonals.\n')
f.write('; Top left from the main diagonal, including it:\n')
for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(j,i+j,j+k,i+j+k))
    f.write(')))')
    nl(f)
nl(f)
f.write('; the other direction, but same orientation of the diagonal:\n')
for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(j+k,i+j+k,j,i+j))
    f.write(')))')
    nl(f)
nl(f)

f.write('; Bottom right from the main diagonal, not including:\n')
for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(i+j,j,i+j+k,j+k))
    f.write(')))')
    nl(f)
nl(f)
f.write('; the other direction, but same orientation of the diagonal:\n')
for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(i+j+k,j+k,i+j,j))
    f.write(')))')
    nl(f)

nl(f)

f.write('; Now the 90 degree flip for the new orientation!\n')
f.write('; Starting with the upper right half, from and including the main diagonal:\n')
for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(N-j-1,i+j,N-j-k-1,i+j+k))
    f.write(')))')
    nl(f)
nl(f)
f.write('; the other direction, but same orientation of the diagonal:\n')
for i in range(0,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(N-j-k-1,i+j+k,N-j-1,i+j))
    f.write(')))')
    nl(f)
nl(f)

f.write('; Bottom left from the main diagonal, not including:\n')
for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(N-i-j-1,j,N-i-j-k-1,k+i-1))
    f.write(')))')
    nl(f)
nl(f)

f.write('; the other direction, but same orientation of the diagonal:\n')
for i in range(1,N-1):
    f.write('(assert (not (or')
    for j in range(0, N-i):
        for k in range(1,N-j-i):
            f.write(' (and x%iy%i x%iy%i)' %(N-i-j-k-1,k+i-1,N-i-j-1,j))
    f.write(')))')
    nl(f)
nl(f)

f.write("; finally, check if the model is satisfiable and output a model\n")
f.write("(check-sat)\n")
f.write("(get-model)\n")
f.close()
