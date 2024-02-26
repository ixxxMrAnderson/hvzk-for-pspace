#!/usr/bin/python3

import subprocess
import random
import sys
import os

CAQE = 'caqe'
os.chdir(os.path.dirname(sys.argv[0]))

if len(sys.argv) > 1:
    print(f'Usage:\n  {sys.argv[0]}\n\nGenerate random instances and check for consistency. The testcase is written to gen.dimacs .')

def write(clauses, quantifiers):
    with open('gen.qdimacs', 'w') as f:
        f.write(f'p cnf {n} {len(clauses)}\n')
        flag = True
        for qq in quantifiers:
            f.write('ae'[flag] + ' ' + ' '.join(map(str, qq)) + ' 0\n')
            flag = not flag
        for clause in clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')

last_result = -1
def run():
    p = subprocess.run('./solver -s gen.qdimacs'.split(), stdout=subprocess.PIPE)
    if p.returncode:
        return True
    global last_result
    last_result = int(p.stdout)
    satisfiable = last_result > 0
    p = subprocess.run([CAQE, 'gen.qdimacs'], stdout=subprocess.DEVNULL)
    really_satisfiable = p.returncode == 10
    return satisfiable != really_satisfiable
            
def make_smaller(clauses, quantifiers):
    it = 0
    while it < 100 and clauses:
        nclauses = [i.copy() for i in clauses]
        nquantifiers = [i.copy() for i in quantifiers]
        beg = 1 if len(nquantifiers[0]) == 1 else 0
        flag = beg < len(nquantifiers)
        r = random.randrange(2 + flag)
        if r == 0:
            nclauses.pop(random.randrange(len(nclauses)))
        elif r == 1:
            idx = random.randrange(len(nclauses))
            lst = nclauses[idx]
            lst.pop(random.randrange(len(lst)))
            if not lst:
                nclauses.pop(idx)
        else:
            idx = random.randrange(beg, len(nquantifiers))
            lst = nquantifiers[idx]
            lst.pop(random.randrange(len(lst)))
            if not lst:
                nquantifiers.pop(idx)

        write(nclauses, nquantifiers)
        it += 1
        if run():
            it = 0
            clauses, quantifiers = nclauses, nquantifiers
            print('Left:', len(clauses), len(quantifiers))
    write(clauses, quantifiers)
            
count = 0
while True:
    n = random.randrange(3, 10)
    clauses = []
    lst = list(range(n))
    random.shuffle(lst)
    quantifiers = [[lst[0]+1]]
    for i in lst[1:]:
        if random.randrange(2):
            quantifiers.append([i+1])
        else:
            quantifiers[-1].append(i+1)

    while True:
        r = random.randrange(100)
        if r < 5:
            k = 1
        elif r < 20:
            k = 2
        elif r < 50:
            k = 3
        else:
            k = random.randrange(3, n+1)
        clause = random.sample(list(range(n)), k)
        clause = [(i+1 if random.randrange(2) else -i-1) for i in clause]
        clauses.append(clause)
        count += 1
        write(clauses, quantifiers)
        if run():
            print('Found error instance, minimising...')
            make_smaller(clauses, quantifiers)
            sys.exit(0)
        if last_result == 0: break
    print(f'\rTested {count} instances', end='')
    sys.stdout.flush()
        
