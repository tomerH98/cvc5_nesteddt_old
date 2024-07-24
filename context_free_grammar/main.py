from assertion import Assertion   
import numpy as np
import subprocess
from tqdm import tqdm


def process_grammar(grammar_file):
    grammar = {}
    with open(grammar_file) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if "->" not in line or "%" not in line:
                print("Invalid grammar: " + line)
                exit()
            line = line.split("%")
            chance = line[0].strip()
            right = line[1].strip()
            # split the right side
            right = right.split("->")
            noun = right[0].strip()
            args = right[1].strip().split()
            if noun not in grammar:
                grammar[noun] = [(chance, args)]
            else:
                grammar[noun].append((chance, args))
    normalized_grammar = {}
    for key in grammar:
        chances, args = [], []
        for chance, arg in grammar[key]:
            chances.append(float(chance))
            args.append(arg)

        chances = np.array(chances)
        chances /= np.sum(chances)
        normalized_grammar[key] = {"chances": chances, "args": args}
    return normalized_grammar

def create_smt2_file_text(grammar_file, base_file, num_assertions=10):
    grammar = process_grammar(grammar_file)
    lines = []
    with open(base_file, "r") as f:
        lines.extend(f.readlines())

    for _ in range(num_assertions):
        assertion = Assertion(grammar)
        assertion.expand()
        lines.append(assertion.create_smt2_line() + "\n")
    lines.append("(check-sat)\n")

    return "".join(lines)

def generate_smt2(grammar_file, base_file, output_file, num_assertions=10):
    text = create_smt2_file_text(grammar_file, base_file, num_assertions=10)
        
    # Write the content to the output file
    with open(output_file, "w") as f:
        f.write(text)

def main():
    np.random.seed(42)
    num_assertions = 10
    max_line_length = float('inf')
    temp_smt2_with_shortest_max_line = None

    for _ in tqdm(range(100)):
        temp_smt2 = create_smt2_file_text("grammar1.txt", "base1.txt", num_assertions)
        lines = temp_smt2.split("\n")
        longest_line_length = max(len(line) for line in lines)
        
        with open(f"temp_smt2.smt2", "w") as f:
            f.write(temp_smt2)

        temp_smt2 = lines[2:]
        temp_smt2 = "\n".join(temp_smt2)

        with open(f"temp_smt2.smt2", "w") as f:
            f.write(temp_smt2)

        try:            
            #command_cvc5 = ["../build/bin/cvc5", "temp_smt2.smt2"]
            #result = subprocess.run(command_cvc5, capture_output=True, text=True, timeout=5)
            #output_cvc5 = result.stdout
            
            #command_cvc5_nesteddt = ["../build/bin/cvc5", "temp_smt2.smt2", "--nesteddt"]
            #result = subprocess.run(command_cvc5, capture_output=True, text=True, timeout=5)
            #output_cvc5_nesteddt = result.stdout

            #if output_cvc5_nesteddt != output_cvc5:
            #    print("FOUND ONE!!!!")
            #    print(temp_smt2)

            command = ["../../z3/build/z3", "temp_smt2.smt2"]
            result = subprocess.run(command, capture_output=True, text=True, timeout=2)
            output_z3 = result.stdout
        except subprocess.TimeoutExpired:
            if longest_line_length < max_line_length:
                max_line_length = longest_line_length
                temp_smt2_with_shortest_max_line = temp_smt2

    if temp_smt2_with_shortest_max_line:
        print("SMT2 file for which Z3 had no response and the shortest max line:")
        print(temp_smt2_with_shortest_max_line)
        print(f"Length of the longest line: {max_line_length}")

if __name__ == "__main__":
    main()
