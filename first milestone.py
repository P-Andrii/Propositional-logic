# basic operations and the dictionary for summoning them
# effectively is just custom syntax code because it's easier to type op_if() that it is to configure an entire if statement

def op_not(temp_input):
    return not temp_input[0]

def op_or(temp_input):
    return temp_input[0] or temp_input[1]

def op_and(temp_input):
    return temp_input[0] and temp_input[1]

def op_if(temp_input):
    if temp_input[0] is True and temp_input[1] is False:
        return False
    else:
        return True

def op_only_if(temp_input):
    return (temp_input[0] and temp_input[1]) or not (temp_input[0] and temp_input[1])

connective_dictionary = {"-": op_not, "or":op_or, "and":op_and, "=>":op_if, "<=>":op_only_if}

class Domain:
    # The domain class - used as storage of WFF, constants, axioms and rules of inference
    # Currently unused
    def __init__(self):
        self.domain_of_interpretation = []
        self.axioms = []
        self.rules_of_inference = []

class Const:
    # Constant class - used to store data for constant objects and is a target of WFF and quantifiers
    # E.G. "Human" would be a constant, "Is an animal" would be a quantifier, "Is an animal therefore Is alive" would be a WFF
    # currently mostly unused although the rest of the code is written with its existence in mind
    def __init__(self, name, domain: Domain, value=None):
        if name is None:
            exit("Constant cannot be undefined")
        self.name = name
        self.value = value
        self.domain = domain

        self.domain.domain_of_interpretation.append(self)

    def __repr__(self):
        return self.name

class WFF:
    # The pièce de résistance of the code, WFF - Well Formed Formula, sometimes written simply as WF, but we burn people who do that as heretics
    # As mentioned above a WFF is a mathematical way of writing logical clauses
    # "If it's raining then the ground is wet" can be written as (R => W)
    # where R is "It's Raining", W is "The ground is wet" and "=>" is the logical connective for "if, then"
    def __init__(self, domain: Domain, formula):
        debug = True  # a boolean that can be turned on for debug printout
        # WFF's formula and domain in which it can be used
        self.domain = domain
        self.formula = formula

        # a function to find the full list of variables required for this wff, currently turned off due to not being used
        # self.inputs = sorted(set(self.formula.check_inputs()))

        # Tag for future use for whether the WFF can be used as a rule of inference, is off by default
        self.inference_rule_tag = False
        # A list for future use in the calculate function where the WFF will take a series of constants/wffs as it's input
        # Is also used when using the function as a rule of inference to store the variables
        self.variable_list = {}
        self.variable_list_tag = {}
        for i in set(self.extract_inputs(self.formula)):
            self.variable_list[i] = i
            self.variable_list_tag[i] = False

    def reset_variable_list(self):
        for i in self.variable_list.keys():
            self.variable_list[i] = i

    def calculate_node(self, variable_list=None, node=None):
        # The recursive function called for calculating the value of a WFF for a certain list of constants
        # To make it recursive but to avoid making separate functions the function takes 2 optional arguments:
        # Variable list for the first calling of this function which gets saved to the WFF for optimisation
        # And Node used when calling the function recursively to know which sub-part of the formula is being calculated

        debug = True  # a boolean that can be turned on for debug printout
        if node is None:
            node = self.formula
        if variable_list:
            for _, i in enumerate(variable_list):
                self.variable_list[_] = i
        if debug: print(self.variable_list)

        # Temporary variables for the left and right parts of the formula
        temp_1 = node[0]
        temp_2 = node[2]

        # Then for both parts of the formula we check whether they are a sub formula, a constant or a variable
        # Could've turned this part into a separate function but that feels excessive for just 2 uses
        if isinstance(temp_1, list):
            temp_1 = self.calculate_node(node=temp_1) # if it's a list recursively run this function
        elif isinstance(temp_1, Const):
            temp_1 = temp_1.value # if it's a constant check it's value
        elif isinstance(temp_1, int):
            temp_1 = self.variable_list[temp_1].value # if it's a variable check the variable_list for the corresponding constant

        if isinstance(temp_2, list):
            temp_2 = self.calculate_node(node=temp_2)
        elif isinstance(temp_2, Const):
            temp_2 = temp_2.value
        elif isinstance(temp_2, int):
            temp_2 = self.variable_list[temp_2].value

        # reset the variable list just in case
        self.reset_variable_list()

        # In the connective_dictionary find the function corresponding to the string in the middle of the formula
        return connective_dictionary[node[1]]([temp_1, temp_2])

    def extract_inputs(self, node):
        # a function to find all the variables used in the function
        temp = []
        if isinstance(node, list):
            # .extend is a very niche function for when a function returns a list, and you need to add it to an existing list in a function that summoned it
            temp.extend(self.extract_inputs(node[0]))
            temp.extend(self.extract_inputs(node[2]))
        elif isinstance(node, int):
            temp.append(node)
        return temp

    def inference_tag_check(self):
        # a function to check if the WFF can be used as an inference rule
        # My assumption is that a WFF can be used as an inference rule if it's a tautology and all the variables on the right
        # are also present on the left
        # currently only checks the variables, still need to implement a check if the WFF is a tautology
        if set(self.extract_inputs(self.formula[2])).issubset(self.extract_inputs(self.formula[0])):
            self.inference_rule_tag = True

    def inference_apply(self, *args):
        # the function to be called from outside to apply the WFF as an inference rule to the WFF that are passed as *arguments
        # *args is used instead of regular arguments because this allows for infinite number of input WFF
        debug = True # a boolean that can be turned on for debug printout
        if self.inference_rule_tag is False:
            return None

        for input_wff in args:
            # for every input WFF we use the recursive inference function
            # the recursive inference function will either return False if the input function cannot be substituted anywhere
            # within the rule of inference WFF, or return the sub formula that can be replaced with the input wff
            # if it doesn't output False then we use the variable list to store which variables get replaced
            x = self.inference_recursive(self.formula[0], input_wff.formula)
            if x is not False:
                self.inference_substitution(x, input_wff.formula)
            if debug: print(f"{input_wff} applied at {x}", f"new variable list:{self.variable_list}")

        # after every input WFF have found their place within the rule of inference WFF we check if all variables have found
        # a constant to be replaced with

        if False in self.variable_list_tag.values():
            self.reset_variable_list()
            return False
        else:
            temp = self.inference_result(self.formula[2])
            self.reset_variable_list()
            return temp

    def inference_recursive(self, node, input_wff):
        # this is the recursive function that tries to find the position of the "node" that can be replaced with the input wff
        if self.inference_check_node(node, input_wff):
            # if the current position can be replaced with the input wff it will return the node
            return node
        else:
            # otherwise it will try to find the node that can be replaced within it's left and right hand side and pass the result
            # that either being False or the correct node position
            answer = False
            if isinstance(node[0], list):
                answer = self.inference_recursive(node[0], input_wff)
            if isinstance(node[2], list) and answer is False:
                answer = self.inference_recursive(node[2], input_wff)
            return answer

    def inference_check_node(self, node, input_wff):
        debug = False # a boolean that can be turned on for debug printout
        if debug: print(node, input_wff)

        # a part of flag that indicate whether the left and right parts of the node can be replaced with the
        # left and right parts of the input wff respectively
        node1_flag = False
        node2_flag = False

        if node[1] != input_wff[1]: # check if the node and input wff have the same operation type
            return False
        else:
            if debug: print(f"{input_wff} fits {node}")

            # same kind of node sub formula checking as in the calculate function
            # e.g. check on the left and right side if they are variables/constants/sub-formulas and then act accordingly
            
            # check if it's a variable
            if isinstance(node[0], int):
                if self.variable_list_tag[node[0]] is False or self.variable_list[node[0]] == input_wff[0]:
                    # check if the variable have already been replaced, which would be indicated by changes in the variable list tags
                    # and if so, check if it has been replaced with a variable that it's about to be replaced with
                    node1_flag = True
                else:
                    node1_flag = False
            
            # check if it's a constant
            elif isinstance(node[0], Const):
                # if the left side is a constant check if it's trying to be replaced by the same constant
                if node[0] == input_wff[0]:
                    node1_flag = True
                else:
                    node1_flag = False
            
            # check if it's a sub-formula
            elif isinstance(node[0], list):
                # if the left side is a list then recursively apply this function to it and the left side of the input wff
                if isinstance(input_wff[0], list):
                    node1_flag = self.inference_check_node(node[0], input_wff[0])
                else:
                    node1_flag = False

            # below is the copy of the code above for the right hand side
            if isinstance(node[2], int):
                if self.variable_list_tag[node[2]] is False or self.variable_list[node[2]] == input_wff[2]:
                    node2_flag = True
                else:
                    node2_flag = False
            elif isinstance(node[2], Const):
                if node[2] == input_wff[2]:
                    node2_flag = True
                else:
                    node2_flag = False
            elif isinstance(node[2], list):
                if isinstance(input_wff[2], list):
                    node2_flag = self.inference_check_node(node[2], input_wff[2])
                else:
                    node2_flag = False

        # if both sides can be replaced by the sides of the input wff and it has the same operation then it returns true
        if node1_flag and node2_flag: return True
        else: return False

    def inference_substitution(self, node, input_wff):
        # this is the function for when the correct position for the input wff has been found within the rule of inference WFF
        # this function scans the correct node for variables and replaces them with respective parts of the input wff
        # that either being a constant, a variable (W.I.P.), or a sub formula
        if isinstance(node[0], int):
            self.variable_list[node[0]] = input_wff[0]
            self.variable_list_tag[node[0]] = True
        elif isinstance(node[0], list):
            self.inference_substitution(node[0], input_wff[0])
        if isinstance(node[2], int):
            self.variable_list[node[2]] = input_wff[2]
            self.variable_list_tag[node[2]] = True
        elif isinstance(node[2], list):
            self.inference_substitution(node[2], input_wff[2])

    def inference_result(self, output_wff):
        # this function is used last in the inference sequence, and it calculates what the resulting function is
        # it uses the same "check if variable/const/sub-formula" as the other functions and is used recursively
        # here output wff is the right side of the inference rule WFF, where each variable gets replaced with a variable
        # from a constant/variable from the variable list
        temp = ["left", output_wff[1], "right"]
        if isinstance(output_wff[0], int):
            temp[0] = self.variable_list[output_wff[0]]
        elif isinstance(output_wff[0], Const):
            temp[0] = output_wff[0]
        elif isinstance(output_wff[0], list):
            temp[0] = self.inference_result(output_wff[0])

        if isinstance(output_wff[2], int):
            temp[2] = self.variable_list[output_wff[2]]
        elif isinstance(output_wff[2], Const):
            temp[2] = output_wff[2]
        elif isinstance(output_wff[2], list):
            temp[2] = self.inference_result(output_wff[2])

        return temp

    def __repr__(self):
        # a small function for easier reading of the WFF, if you use "print(A)", where A is a wff you'll get an output
        # of the form "(0 => 1) [0, 1]" instead of the weird "(Object 128h0c1n at register 180cn239uf2)" that python usually uses
        return repr(self.formula)# + " " + str(self.inputs)

def main():
    # example code used for debugging
    domain_1 = Domain() # creating an empty domain

    # a and b are constants used in the calculation example, they can also be used in the rule of inference example
    a = Const("a", domain_1, True)
    b = Const("b", domain_1, True)

    # wff_1 is the WFF that will be used as an example of a rule of inference
    # wff_2 and wff_3 will be used as examples of possible WFF that are subject to a rule of inference
    # "a", "b" and "c" here can be replaced with any text/constant (for example the a and b constants from above)
    wff_1 = WFF(domain_1, [ [[0, "=>", 1], "and", [1, "=>", 2]], "=>", [0, "=>", 2] ])
    wff_2 = WFF(domain_1, [ "a", "=>", "b"])
    wff_3 = WFF(domain_1, ["b", "=>", "c"])
    wff_1.inference_tag_check()
    print(wff_1.inference_apply(wff_2, wff_3))

    # simple calculation example
    wff_4 = WFF(domain_1, [0, "and", 1])
    print(wff_4.calculate_node([a,b]))

    # rule of inference with a more general use, where instead of constants the input wff have variables
    wff_5 = WFF(domain_1, [0, "=>", 1])
    wff_6 = WFF(domain_1, [1, "=>", 2])
    print(wff_1.inference_apply(wff_5, wff_6))

if __name__ == "__main__":
    main()
