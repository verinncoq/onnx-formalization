import sys
import time


def main():
    # check for correct number of arguments
    if (len(sys.argv) != 4):
        print("Expected 3 arguments instead of", len(sys.argv) - 1)
        print("Please use the following program call:", sys.argv[0], "<input file> <output file> <definition_name>")
        return

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    definition = sys.argv[3]

    # check for same name of input file and output file (since I dont know what will happen this is forbidden)
    if (input_file == output_file):
        print("Input file and output file can not be the same")
        return

    # try to open the input file, raise error when not exist
    try:
        f = open(sys.path[0] + input_file, "r")
        file = f.read()
    except FileNotFoundError:
        print("The file", input_file, "does not exist.")
        return

    # checks if output file already exists, if so ask user if it should be overwritten
    try:
        out = open(sys.path[0] + output_file, "x")
    except FileExistsError:
        cont = input(
            "<" + output_file + "> already exists. Do you wish to continue? (<" + output_file + "> will be overwritten.) [y/n]: ")
        while (True):
            if (cont == "n" or cont == "N" or cont == "no" or cont == "No"):
                print("Process has been terminated by user, no files written.")
                return
            elif (cont == "y" or cont == "Y" or cont == "yes" or cont == "Yes"):
                out = open(sys.path[0] + output_file, "w")
                break
            else:
                cont = input("please type <y> or <n>: ")

    # double the quotation mark, so Rocq doesnt interpret them as string endings
    file = file.replace('"', '""')

    # get time of creation (inspired by https://www.geeksforgeeks.org/time-strftime-function-in-python/)
    t = time.gmtime()
    format_time = time.strftime("%Y-%m-%d %H:%M:%S", t)

    pre = """(*this file was generated automatically by """ + sys.argv[0] + """*)
From Coq Require Import Strings.String.
Open Scope string_scope.

(*converted on """ + format_time + """ UTC*)
(*slightly modified to be readable in rocq*)

Definition """ + definition + """ := "
"""

    after = """"."""

    output = pre + file + after

    # write file
    try:
        out.write(output)
    except Exception as e:
        print("something went wrong during file writing:")
        print(e)
        return

    print("converted successfully")


main()
