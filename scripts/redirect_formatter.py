import sys
import time

def cut_between_quotation_mark(string):
    first_index = string.find('"')
    last_index = len(string) - string[::-1].find('"') #string gets reversed, so last one is found
    if(string.find('"') == -1):
        last_index = -1
    if(first_index == -1):
        return ""
    elif(last_index == -1):
        return ""
    elif(first_index > last_index):
        return ""
    else:
        return string[first_index+1:last_index-1]

def main():
    #check for correct number of arguments
    if(len(sys.argv) != 3):
        print("Expected 2 arguments instead of", len(sys.argv)-1)
        print("Please use the following program call:", sys.argv[0] , "<input file> <output file>")
        return

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    #check for same name of input file and output file (since I dont know what will happen this is forbidden)
    if(input_file == output_file):
        print("Input file and output file can not be the same")
        return

    #try to open the input file, raise error when not exist
    try:
        f = open(sys.path[0] + input_file, "r")
        file = f.read()
    except FileNotFoundError:
        print("The file", input_file, "does not exist.")
        return

    #checks if output file already exists, if so ask user if it should be overwritten
    try:
        out = open(sys.path[0] + output_file, "x")
    except FileExistsError:
        out = open(sys.path[0] + output_file, "w")


    #un-double the quotation mark, so Rocq interprets them as string endings again
    file = file.replace('""', '"')
    
    #use only the part between the quotation marks
    file = cut_between_quotation_mark(file)

    #get time of creation (inspired by https://www.geeksforgeeks.org/time-strftime-function-in-python/)
    t = time.gmtime()
    format_time = time.strftime("%Y-%m-%d %H:%M:%S", t)

    

    pre = """(*this file was generated automatically by """+sys.argv[0]+""" on """+format_time+""" UTC*)

"""

    output = pre + file
    
    #write file
    try:
        out.write(output)
    except Exception as e:
        print("something went wrong during file writing:")
        print(e)
        return
    
    print("converted successfully")
    
main()
