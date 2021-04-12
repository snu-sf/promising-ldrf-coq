import sys, re

if len(sys.argv) != 4:
    print ("Usage: " + sys.argv[0] + " infile outfile file_num")
    sys.exit(1)

arg_infile = sys.argv[1]
arg_outfile = sys.argv[2]
file_num = sys.argv[3]

DEBUG = 0

S_NONE      = 0
S_LABEL     = 1
S_LDXR      = 2
S_CMP       = 3
S_ARITH     = 5
S_STXR      = 6
S_CBNZ      = 7

nline = 0
nlabel = 0
insert = 0
status = S_NONE


with open(arg_infile, 'r') as infile, open(arg_outfile, 'w') as outfile:
    for line in infile:
        nline += 1

        while True:
            # EMPTY or COMMENT
            match = re.search('^\s*(//.*)?$', line)
            if match:
                if (DEBUG):
                    print ("EMPTY or COMMENT: " + line)
                break

            # LABEL
            match = re.search('^\s*(\S+):\s*(//.*)?$', line)
            if match:
                if status == S_NONE or status == S_LABEL:
                    r_label_1 = match.group(1)
                    status = S_LABEL
                    if (DEBUG):
                        print ("LABEL: " + r_label_1)
                    break
                print ("Error in " + arg_infile + ":" + "LABEL during RMW" + ":" + str(nline) + ": " + line)
                sys.exit(1)

            # LDXR
            match = re.search('^\s*ldxr\s+(\S+),\s+\[(\S+)\]\s*(//.*)?$', line)
            if match:
                if status == S_NONE or status == S_LABEL:
                    r_ldxr_1 = match.group(1)
                    r_ldxr_2 = match.group(2)
                    if r_ldxr_2 != r_ldxr_1:
                        status = S_LDXR
                        if (DEBUG):
                            print ("LDXR: " + r_ldxr_1 + " " + r_ldxr_2)
                        break
                print ("Error in " + arg_infile + ":" + "LDXR" + ":" + str(nline) + ": " + line)
                sys.exit(1)
                        

            # CMP or CB(N)Z or ARITHMETIC
            if status == S_LDXR:
                match = re.search('^\s*cmp\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_cmp_1 = match.group(1)
                    r_cmp_2 = match.group(2)
                    if r_cmp_1 == r_ldxr_1:
                        status = S_CMP
                        if (DEBUG):
                            print ("CMP: " + r_cmp_1 + " " + r_cmp_2)
                        break
                match = re.search('^\s*cbn?z\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_cbnz_m_1 = match.group(1)
                    r_cbnz_m_2 = match.group(2)
                    if r_cbnz_m_1 == r_ldxr_1:
                        status = S_NONE
                        if (DEBUG):
                            print ("CBNZ_M: " + r_cbnz_m_1 + " " + r_cbnz_m_2)
                        break
                match = re.search('^\s*(add|adds|sub|subs|and|ands|eor|orr|tst)\s+(\S+),\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_add_1 = match.group(2)
                    r_add_2 = match.group(3)
                    r_add_3 = match.group(4)
                    if r_add_2 == r_ldxr_1 or r_add_3 == r_ldxr_1:
                        status = S_ARITH
                        if (DEBUG):
                            print ("ARITH: " + r_add_1 + " " + r_add_2 + " " + r_add_3)
                        break
                    elif r_add_1 != r_ldxr_1:
                        if (DEBUG):
                            print ("ARITH: " + r_add_1 + " " + r_add_2 + " " + r_add_3)
                        break
                match = re.search('^\s*stl?xr\s+(\S+),\s+(\S+),\s+\[(\S+)\]\s*(//.*)?$', line)
                if match:
                    r_stxr_1 = match.group(1)
                    r_stxr_2 = match.group(2)
                    r_stxr_3 = match.group(3)
                    if r_stxr_3 == r_ldxr_2:
                        status = S_STXR
                        if (DEBUG):
                            print ("STXR: " + r_stxr_1 + " " + r_stxr_2 + " " + r_stxr_3)
                        break
                match = re.search('^\s*mov\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_mov_1 = match.group(1)
                    if r_mov_1 == r_ldxr_1:
                        print("Error in " + arg_infile + ":" + "MOV overwrites" + ":" + str(nline) + ": " + line)
                    break;
                print ("Error in " + arg_infile + ":" + "STXR" + ":" + str(nline) + ": " + line)
                sys.exit(1)
                print ("Error in " + arg_infile + ":" + "CMP/CB(N)Z/ARITH/STXR" + ":" + str(nline) + ": " + line)
                sys.exit(1)

            # BEQ/BNE
            if status == S_CMP:
                match = re.search('^\s*(b\.eq|b\.ne)\s+(\S+)\s*(//.*)?$', line)
                if match:
                    status = S_NONE
                    if (DEBUG):
                        print ("BNE: " + r_bne_1)
                    break
                print ("Error in " + arg_infile + ":" + "BEQ/BNE" + ":" + str(nline) + ": " + line)
                sys.exit(1)

            # STXR
            if status == S_ARITH:
                match = re.search('^\s*stl?xr\s+(\S+),\s+(\S+),\s+\[(\S+)\]\s*(//.*)?$', line)
                if match:
                    r_stxr_1 = match.group(1)
                    r_stxr_2 = match.group(2)
                    r_stxr_3 = match.group(3)
                    if r_stxr_3 == r_ldxr_2:
                        status = S_STXR
                        if (DEBUG):
                            print ("STXR: " + r_stxr_1 + " " + r_stxr_2 + " " + r_stxr_3)
                        break
                print ("Error in " + arg_infile + ":" + "STXR" + ":" + str(nline) + ": " + line)
                sys.exit(1)

            # MOV
            if status == S_STXR:
                match = re.search('^\s*mov\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_mov_1 = match.group(1)
                    if r_mov_1 == r_ldxr_1:
                        print("Error in " + arg_infile + ":" + "MOV overwrites" + ":" + str(nline) + ": " + line)
                    break;
                
            # CBNZ
            if status == S_STXR:
                match = re.search('^\s*cbnz\s+(\S+),\s+(\S+)\s*(//.*)?$', line)
                if match:
                    r_cbnz_1 = match.group(1)
                    r_cbnz_2 = match.group(2)
                    if r_cbnz_1 == r_stxr_1 and r_cbnz_2 == r_label_1:
                        status = S_NONE
                        insert = 1
                        if (DEBUG):
                            print ("CBNZ: " + r_cbnz_1 + " " + r_cbnz_2)
                        break
                print ("Error in " + arg_infile + ":" + "CBNZ SUCC BIT" + ":" + str(nline) + ": " + line)
                sys.exit(1)

            status = S_NONE
            break

        outfile.write(line)
        if (insert):
            flabel = ".L" + "FAKE" + str(file_num) + "_" + str(nlabel)
            fake1 = "// fake branch\n"
            fake2 = "\tcbnz\t" + r_ldxr_1 + ", " + flabel + "\n"
            fake3 = flabel + ":" + "\n"
            outfile.write(fake1)
            outfile.write(fake2)
            outfile.write(fake3)
            nlabel += 1
            insert = 0
