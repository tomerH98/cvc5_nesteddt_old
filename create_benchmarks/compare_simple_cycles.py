import time
from tqdm import tqdm
import subprocess

def create_cycle(n):
    smt_code = "(set-logic ALL)\n(declare-datatypes ((T 0)) (((nT) (cons (id Int) (arr (Array Int T)) ) ) ))\n"
    for i in range(n):
        smt_code += f"(declare-const x{i} T)\n"
        smt_code += f"(declare-const a{i} (Array Int T))\n"
    
    smt_code += "\n"
    
    for i in range(n):
        smt_code += f"(assert (= a{i} (arr x{i})))\n"
        smt_code += f"(assert (= x{(i + 1) % n} (select a{i} {i})))\n"

    for i in range(n):
        smt_code += f"(assert (not (= nT x{i})))\n"
    
    smt_code += "(check-sat)\n"
    
    return smt_code

def run_benchmark(n):
    # Create benchmark file
    filename = f"benchmark.smt2"
    with open(filename, 'w') as file:
        file.write(create_cycle(n))

    # Run Z3 solver
    start_time = time.time()
    result_z3 = subprocess.run(["/root/z3/build/z3", filename], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    time_z3 = time.time() - start_time
    output_z3 = result_z3.stdout.decode().strip()
    if output_z3 != "unsat":
        print("z3", output_z3)
        raise Exception("Z3 didn't return unsat")

    # Run CVC5 solver
    start_time = time.time()
    result_cvc5 = subprocess.run(["/root/cvc5_nesteddt/build/bin/cvc5", filename, "--nesteddt", "--dt-blast-splits"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    time_cvc5 = time.time()  - start_time
    output_cvc5 = result_cvc5.stdout.decode().strip()
    if output_cvc5 != "unsat":
        print("cvc5", output_cvc5)
        raise Exception("CVC5 didn't return unsat")

    return {"z3":time_z3, "cvc5":time_cvc5}

if __name__ == "__main__":
    ns = range(10, 401, 10)
    times_z3 = []
    times_cvc5 = []

    for n in tqdm(ns):
        d = run_benchmark(n)
        times_z3.append(d["z3"])
        times_cvc5.append(d["cvc5"])

    # Format the results
    z3_results = "coordinates {\n" + " ".join([f"({n},{t})" for n, t in zip(ns, times_z3)]) + "\n};\n"
    cvc5_results = "coordinates {\n" + " ".join([f"({n},{t})" for n, t in zip(ns, times_cvc5)]) + "\n};\n"

    # Save the results to a file
    with open("results.txt", 'w') as file:
        file.write("z3 = \n")
        file.write(z3_results)
        file.write("\ncvc5 = \n")
        file.write(cvc5_results)
