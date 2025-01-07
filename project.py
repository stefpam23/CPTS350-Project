from pyeda.inter import *
import typing

def is_prime(val:int): # verifies if the value targeted is a prime number
    if val < 3: return False
    for num in range(2, val // 2 + 1):
        if val % num == 0:
            return False 
    return True

def encode_bin(num:int, prefix:str=None): # Encode the binary string to boolean formula param[0] - binary string, param[1] - prefix for encode
    if prefix is None: prefix = 'x'   #default to x
    bin_str = format(num, '05b')
    encoded = []
    for i, c in enumerate(bin_str): # 1 is the lowest index
        index = i + 1  # binary either 1 or 0
        Verify_index = prefix
        if c == '0':Verify_index = '~' + Verify_index + str(index) # if 0, start with ~
        else: Verify_index = Verify_index + str(index)
        encoded.append(Verify_index) 
    return "&".join(encoded)

def build_edges(): # Collect all edges by definition an edge i->j iff (i+3)%32 == j%32 or (i+8)%32 == j%32
    list_edges = []
    for i in range(0, 32):
        for j in range(0, 32):
            if (i+3)%32 == j%32 or (i+8)%32 == j%32:
                end_X = encode_bin(i, 'x') # encode to x
                end_Y = encode_bin(j, 'y') # encode to y
                edge = end_X + '&' + end_Y
                list_edges.append(edge)
    return '|'.join(list_edges)

def encode_to_bool(lst:list, prefix:str): # bool formula in string
    res = []
    for val in lst:
        end_val = encode_bin(val, prefix)
        res.append(end_val)
    return '|'.join(res)

def build_BDD(boolexpr): # Convert bool_expr in string to Expression then convert to BDD object
    expression = expr(boolexpr)
    bdd = expr2bdd(expression)
    return bdd

def build_BDDcompose(bdd1:object, bdd2:object): # compose y to z for BDD1, x to Z for BDD2 then smoothing all Z
    Z = [bddvar("z1"), bddvar("z2"), bddvar("z3"), bddvar("z4"), bddvar("z5")]
    X = [bddvar("x1"), bddvar("x2"), bddvar("x3"), bddvar("x4"), bddvar("x5")]
    Y = [bddvar("y1"), bddvar("y2"), bddvar("y3"), bddvar("y4"), bddvar("y5")]
    b1 = bdd1.compose({Y[0]:Z[0], Y[1]:Z[1], Y[2]:Z[2], Y[3]:Z[3], Y[4]:Z[4]})
    b2 = bdd2.compose({X[0]:Z[0], X[1]:Z[1], X[2]:Z[2], X[3]:Z[3], X[4]:Z[4]})
    return (b1 & b2).smoothing(Z) 

def get_transitive_closure(bdd:object): # U -> V if u -> v within m-1 steps where m = # nodes in G
    H = bdd
    while True:
        Hp = H 
        H = Hp or build_BDDcompose(Hp, bdd)
        if H.equivalent(Hp):
            break 
    return H # The fixpoint BDD for some n

def statementA_verify(RR2star:object, PRIME:object, EVEN:object):
    print("Verifying Statement A")
    # for all u, (if PRIME(u) -> thee exists v such that EVEN(v) AND RR2star(u,v))
    U = [bddvar("x1"), bddvar("x2"), bddvar("x3"), bddvar("x4"), bddvar("x5")]
    V = [bddvar("y1"), bddvar("y2"), bddvar("y3"), bddvar("y4"), bddvar("y5")]
    answer = (~PRIME) | ((EVEN & RR2star).smoothing(V)) # Equivalent to evaluate the BDDconstant.
    print("Statement A is: {}".format(answer.equivalent(True)))
    
### Test Case Functions (For 3.1 and 3.2)

def testcases3_1(RR:object, PRIME:object, EVEN:object): #For 3.1
    RRtest = [(27,3), (16,20)]
    EVENtest = [14, 13] 
    PRIMEtest = [7, 2] 
    print("Testcases 3.1 for BDDs")
    for x, y in RRtest:  #RR(27,3) and RR(16,20)
        formula = encode_bin(x, 'x') + '&' + encode_bin(y, 'y') #encode values in binary
        curated_bdd = build_BDD(formula) #build BDD from the formula
        resultedBDD = curated_bdd & RR 
        # AND the two BDD, if there exist a solution return True
        print("RR({}, {}) is:\t {}".format(x, y, resultedBDD.satisfy_count() > 0)) #Prints true or false for the test case if it is valid for the paths
      
    for num in EVENtest: #EVEN(14) and EVEN(13)
        formula = encode_bin(num, 'y')
        curated_bdd = build_BDD(formula)
        resultedBDD = curated_bdd & EVEN
        print("EVEN({}) is:\t {}".format(num, resultedBDD.satisfy_count() > 0))
    
    for num in PRIMEtest: #PRIME(7) and PRIME(2)
        formula = encode_bin(num, 'x')
        curated_bdd = build_BDD(formula)
        resultedBDD = curated_bdd & PRIME
        print("PRIME({}) is:\t {}".format(num, resultedBDD.satisfy_count() > 0))

def testcases3_2(RR2:object):
    print(" Testcases 3.2 for RR2")
    cases = [(27,6), (27,9)]
    for x, y in cases:
        formula = encode_bin(x, 'x') + '&' + encode_bin(y, 'y')
        curated_bdd = build_BDD(formula)
        resultedBDD = curated_bdd & RR2
        print("RR2({}, {}) is:\t {}".format(x, y, resultedBDD.satisfy_count() > 0))

### Main Function Calling

# even and prime numbers from 0 to 31
evenlst = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24 , 26, 28, 30]
primelst = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

# For 2
R = build_edges()  
prime = encode_to_bool(primelst, 'x')  # for statement A usage name prime x
even = encode_to_bool(evenlst , 'y')   # for statement A usage name even y

# Print out formulas for reference
print("R boolean formula:\t {}\n".format(R))
print("prime boolean formula:\t {}\n".format(prime))
print("even boolean formula:\t {}\n".format(even))

# For 3.1 (and test cases)
RR = build_BDD(R)
PRIME = build_BDD(prime)
EVEN = build_BDD(even) 
testcases3_1(RR, PRIME, EVEN)

# For 3.2 (and test cases)
RR2 = build_BDDcompose(RR, RR)
testcases3_2(RR2)

# For 3.3
RR2star = get_transitive_closure(RR2)

# For 3.4
statementA_verify(RR2star, PRIME, EVEN)


    
