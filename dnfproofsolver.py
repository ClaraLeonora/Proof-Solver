from sympy import symbols, Or, Not, to_dnf, Implies, And, simplify
from sympy.logic.boolalg import Implies

# Make sure Python > Terminal: Activate Env in Current Terminal on load
# is selected in you conda activate base setting search. 

def group_terms(line):
    """
    Symbols delimited by AND are a single term.  
    Symbols delimited by OR a different terms. 

    Parameters: The premise line to group terms. 
    line: SymPy logic statement. 

    Returns: 
    List: of terms in the line. 
    """

    if isinstance(line, Or):
        return list(line.args)
    else:
        return [line]

def step_four(conc_terms, given_terms):
    """
    Starting from the most-recently generated proof line, 
    look for a proof line that contains the first term (T1) of the conclusion. 
    Call this Line A.  

    Parameters:
    conc_terms: List of terms in the conclusion. 
    given_terms: List of terms in the givens. 

    Returns: 
    line A which includes T1. 
    """
    # (T1) of the conclusion. 
    T1 = conc_terms[0]
    print("\nFirst term in conclusion to find:", T1)
    line_A_terms = None
    line_A = None
    # Look for a term that matches T1 of the conclusion. 
    for i in range(len(given_terms)):
        for j in range(len(given_terms[i])):
            # Call this Line A
            if (T1 == given_terms[i][j]):
                line_A = given_dnf[i]

    return line_A


def step_five(conc_terms, line_A_terms):
    """
    Identifies TElim (T2) by finding the first term not in the conclusion
    on line A. 

    Parameters:
    conc_terms: list of terms in the conclusion. 
    line_A_terms: list of terms in line A. 

    Returns:
    TElim term found in line A. If not found, returns None.  
    """
    
    # Find TELIM (T2), first term not in conclusion on Line A.

    # Iterate through to find TElim:
    for term in line_A_terms:
        if term not in conc_terms:
            return term
            
    return None


def step_six(given_terms, TElim):

    """
    Looks for a proof line that contains -TElim. Call this line B. 
    Iterate through given terms to find -TElim. 

    Parameters: 
    TElim: The term we are looking to eliminate
    given_terms: nested list of the terms in the given. Each line is a seperate list.

    Returns:
    Line B symbolic logic which can then be grouped into terms with the group_terms method.
    Line B is returned None of no terms were found.   
    """

    line_B = None
    line_B_terms = None

    for i in range(len(given_terms)):
        for j in range(len(given_terms[i])):
            # Call this Line A
            if (Not(TElim) == given_terms[i][j]):
                line_B_terms = given_terms[i]
                line_B = given[i]

    # Call this line_B

    if line_B == None:
        return None

    else:
        print("LineB is :", line_B, "with terms: ", line_B_terms)
        return line_B

def step_seven(TElim, line_A, line_B):
    """
    Combine with the Barnes Rule: 
    (TElim + restofA) & (-TElim+ restofB) => (T2 * -T2) + restofA + restofB 
    Since terms are AND'd together, replace TElim term with False to neutralize it.

    Paramters: 
    TElim: The term we want to eliminate. 
    line_A: Where we found TElim. 
    line_B: Where we found -TElim.  

    Returns: 
    The new LineA to be compared to the conclusion.
    """

    restofA = simplify(line_A.subs(TElim, False))
    restofA_terms = group_terms(restofA)

    restofB = simplify(line_B.subs(Not(TElim), False))
    restofB_terms = group_terms(restofB)

    print("Rest of Line A is:", restofA, ", with terms:", restofA_terms)
    print("Rest of Line B is:", restofB, ", with terms:", restofB_terms)

    # (TElim + restofA) & (-TElim+ restofB) => (T2 * -T2) + restofA + restofB 
    line_A = simplify(Or(And(TElim, Not(TElim)), restofA, restofB))
    return line_A


def five_six_seven(conc_terms, line_A, line_A_terms):
    """
    Calculates if the proof has been completed. 
    If the proof has not been completed, calls steps 5 through 7 recursively. 

    Parameters: 
    conc_terms: list of the terms in the conclusion. 
    line_A_terms: list of the terms in line A. 
    line_A: in symbolic logic. 

    Returns:
    Boolean: True if the proof is complete.
    False if there is no proof that satisfies the givens and the conclusion.  
    """

    # Base case.
    # Sort terms in line A and conclusion. 
    #line_A_terms.sort()
    #conc_terms.sort()

    # Check if term lists are identical (that's when we're done)
    if (line_A_terms == conc_terms):
        print("You have proven the conclusion")
        return True

    #Recursive call for steps 5 through 7. 
    else:
        print("Steps 5 through 7 repeat.")
        
        # STEP 5
        TElim = step_five(conc_terms, line_A_terms)
        T2 = step_five(conc_terms, line_A_terms)

        # If no TELim was found, print there is no proof and return None. 
        if (TElim == None):
            print("TELim not found.")
            return False

        # STEP 6: 
        line_B = step_six(given_terms, TElim)
        if line_B == None:
            print("-TElim not found.")
            return False
        line_B_terms = group_terms(line_B)

        # STEP 7: 
        line_A = step_seven(TElim, line_A, line_B)
        if line_A == None:
            print("There is no line A.")
            return False
        line_A_terms = group_terms(line_A)
        
        print("The new LineA is", line_A)
        print("Terms in LineA are", line_A_terms)

        # Recursive call to check if proof has ended. 
        five_six_seven(conc_terms, line_A, line_A_terms)

# Directions for entering SymPy logic. 
print("Please enter your boolean statement givens and conclusion in SymPy logic format:\n",
     "\nA AND B: And(A, B)",
     "\nA OR B: Or(A, B)",
     "\nA IMPLIES B: Implies(A, B)",
     "\nA IF AND ONLY IF B: Equivelent(A, B)",
     "\nNOT A: Not(A)\n")


# Prompts user to enter the number of givens they want. 
num_givens = input("How many givens are there? ")
num_givens = int(num_givens)
count = 1
given = []

# Prompts user to enter the givens. 
 
while count <= num_givens:
    user_input = input("Enter a given as a boolean statement: ")
    try:
        parsed_input = simplify(user_input)
        given.append(parsed_input)
        count += 1
    except:
       print("Please enter a valid boolean statement.") 

count = 0
while count < 1:
    user_input = input("Enter a conclusion as a boolean statement: ")
    try:
        conc = simplify(user_input)
        count+=1
    except:
        print("Please enter a valid boolean statement.")


# STEP 1: convert givens to DNF
# Use to_dnf to convert givens to dnf. 
given_dnf = [to_dnf(g) for g in given]

# STEP 2: Convert conclusion to DNF
# Use to_dnf to convert conclusion to dnf. 
conc_dnf = to_dnf(conc)

# Print out dnf givens
for i in range (len(given)):
    print("Line", i + 1, "in DNF: ", given_dnf[i])

# Print out DNF conclusion: 
print("Conclusion in DNF:", conc_dnf, "\n")

#STEP 3: Identify terms in given and conclusion. 
# List of terms for each given. 

# Creates a list of terms for each given. 
given_terms = [group_terms(given) for given in given_dnf]
conc_terms = group_terms(conc_dnf)

# Prints Givens terms: 
for i in range(len(given_terms)):
    print("Line", i + 1, "terms:", end=" ")
    for j in range(len(given_terms[i])):
        print(given_terms[i][j])

# Prints conclusion terms:
print("Conclusion terms:", end=" ")
for i in range(len(conc_terms)):
    print(conc_terms[i])

#STEP 4:  
# (T1) of the conclusion. 
line_A = step_four(conc_terms, given_terms)
line_A_terms = group_terms(line_A)
print("Line A is", line_A)
print("Line A terms are", line_A_terms)


# STEP (5-7) 8: Now call the result Line A. Repeat 5-7 
five_six_seven(conc_terms, line_A, line_A_terms)







