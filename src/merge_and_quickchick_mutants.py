import sys
import argparse
import os
import subprocess
import tempfile

# Given 'Require Import ..', drop mutated files from import list
def modify_line(line, mutated_files):
    import_stmt = 'Require Import'
    if line.startswith(import_stmt):
        imports = line.rstrip()[0:-1].split()[2:]
        lines = ''
        for name in imports:
            file = name.split('.')[-1]
            if file not in mutated_files:
                new_stmt = import_stmt + ' ' + name + '.'
            else:
                new_stmt = ''
            lines = lines + new_stmt + '\n'
        return lines
    else:
        return line    

def partition_into_mutated_and_static(base_dir):
    files = [filename for filename in os.listdir(base_dir) \
             if not os.path.isdir(filename) and filename.endswith('.v')]
    files_with_mutant, static_files = [], []
    for filename in files:
        with open(os.path.join(base_dir, filename), 'r') as f:
            l = [line for line in f if '(*!' in line]
            # has_mutant = False if [line for line in f if '(*!' in line] == [] else True <- parsing problem?
            has_mutant = False if l == [] else True
            if has_mutant == True:
                files_with_mutant = files_with_mutant + [filename]
            else:
                static_files = static_files + [filename]
    return (files_with_mutant, static_files)

def absolute_of(path):
    if os.path.isabs(path):
        return path
    else:
        return os.path.join(os.getcwd(), path)
    
def process(base_dir, mergedto_filename):
    files_with_mutations, _ = partition_into_mutated_and_static(base_dir)
    print 'Merging the following files with mutants: ' + str(files_with_mutations)

    mutants_filename = ''
    if mergedto_filename == None:
        tmp = tempfile.NamedTemporaryFile()
        mutants_filename = tmp.name
        tmp.close()
    else:
        mutants_filename = absolute_of(mergedto_filename)
    
    with open(mutants_filename, 'w') as fout:
        for input_file in files_with_mutations:
            fout.write('(******** ' + input_file + ' ********)\n\n\n')
            with open(os.path.join(base_dir, input_file), 'r') as fin:
                for line in fin:
                    fout.write(modify_line(line, files_with_mutations))
            fout.write('\n(******** End of ' + input_file + ' ********)\n\n\n')
    print('Merged into file: ' + mutants_filename)
    return mutants_filename

def parse_coqproject(abs_path_to_prof_file):
    args = ''
    with open(abs_path_to_prof_file, 'r') as f:
        for line in f:
            if line.startswith('-R') or line.startswith('-Q'):
                current_dir, _ = os.path.split(abs_path_to_prof_file)
                args = args + line[0:3] + os.path.join(current_dir, line.rstrip()[3:]) + ' '
    return args
            
def run_quickchick(coq_args, mutants_filename):
    quickchick = 'quickChick -I "' + coq_args + '" ' + mutants_filename
    print 'Running: ' + quickchick
    subprocess.call(quickchick, shell=True)
    
def main():
    parser = argparse.ArgumentParser(description= \
                                     'This script parses all Coq files in supplied dir and ' \
                                     'merges those containing mutants into mergedto (if specified), ' \
                                     'then runs QuickChick on it.')
    parser.add_argument('dir', help='directory containing Coq files, e.g. coq/')
    parser.add_argument('--mergedto', help='file to merge Coq files with mutants to')
    parser.add_argument('--proj', default=None, help='relative/absolute path to Coq project file, e.g. _CoqProject')
    parser.add_argument('--coqopts', default='', help='Coq loadpath (e.g. "-I ... -R <physical> <logical> -Q ...")')
    args = parser.parse_args()

    base_dir = absolute_of(args.dir)
    mutants_filename = process(base_dir, args.mergedto)

    coq_args = args.coqopts
    if args.proj != None:
        abs_path_to_proj_file = absolute_of(args.proj)
        coq_args = parse_coqproject(abs_path_to_proj_file)
    
    run_quickchick(coq_args, mutants_filename)

if __name__ == '__main__':
    main()
    

    
