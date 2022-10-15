import json
import os
import sys
import subprocess
import string
from stat import ST_CTIME, S_ISREG, ST_MODE

# Debugging signal
DEBUG = True


# Re-format log file to only include taint analysis result
def trim_log(in_file):
    new_log = ""
    log_lines = open(in_file, "r").readlines()
    taint = False
    entry_point = ""
    # only for debugging, skipp if the file is already trimmed
    if DEBUG and "[kernel]" not in log_lines[0]:
        return
    for line in log_lines:
        if "[eva] Analyzing a complete application starting at" in line:
            entry_point = line.split()[-1]
        if not taint and line.find("# taint") != -1:
            new_log += line
            taint = True
        elif taint:
            new_log += line
            if line.find("==END OF DUMP==") != -1:
                taint = False
                new_log += '\n'
        if "[from] call to" in line:
            func_call = line.split()[3]
            if not func_call.startswith("Frama_C") and func_call not in new_log:
                new_log += "call function " + func_call + "\n"
    new_log += "call function " + entry_point + "\n"
    with open(in_file, "a") as output:
        output.truncate()
        params = os.path.splitext(os.path.basename(in_file))[0].split('_')
        output.write("Log file:%s\nTaint:msg%s\tValue:%s\n\n" % (os.path.abspath(in_file), params[2], params[-1]))
        output.write(new_log)
    return


# Extract taint analysis result and save it as a dict object
def get_taint_info(log_file):
    with open(log_file, "r") as in_file:
        file_lines = in_file.readlines()

    taint_data = {"taint_label": file_lines[1].split()[0].split(":")[1],
                  "msg_value": file_lines[1].split()[1].split(":")[1],
                  "tainted": [], "func_calls": []}

    for line in file_lines[3:]:
        # Address function calls
        if line.startswith("call function"):
            taint_data["func_calls"].append(line.split()[2].rstrip('\n'))
            continue

        # Address taint analysis result
        if "\\nothing" in line:
            continue
        line = line.replace(' ', '')
        while "{" in line:
            new_map = ""
            map_start = line.index('{')
            split_end = line[0:map_start].rfind(";")
            if split_end != -1 and split_end < map_start:
                variables = line[:split_end].split(';')
                if len(variables) != 0:
                    taint_data["tainted"].extend(variables)
                line = line[split_end + 1:]
            else:
                curr_base = ""
                base = ""
                while "{" in line:
                    left = line.index('{')
                    right = line.index('}')
                    if left > right:
                        tmp_line = line[:right + 1]
                        new_map = line[right + 2:]
                        line = tmp_line
                        continue
                    tmp_line = line.split('{', 1)
                    curr_base = tmp_line[0]
                    if ';' in curr_base:
                        taint_data["tainted"].append(base + curr_base[:-1])
                        curr_base = base
                    else:
                        base += curr_base
                    line = tmp_line[1]
                while "}" in line and base != '':
                    offset_end = line.index('}')
                    offsets = line[:offset_end].split(';')
                    for offset in offsets:
                        if offset != '':
                            variable = base + offset
                            taint_data["tainted"].append(variable)
                    base = base.replace(curr_base, "", 1)
                    curr_base = base
                    line = line[offset_end + 1:]
            if new_map and '{' in new_map:
                line = new_map
                continue
        if len(line) > 1 and ';' in line:
            for info in line.rstrip('\n').split(';'):
                if info != '' and info != '}':
                    taint_data["tainted"].append(info)
    taint_data["tainted"] = list(set(taint_data["tainted"]))  # remove duplicates
    # Reformat variable  to match AST format
    for i, var in enumerate(taint_data["tainted"]):
        if var.startswith("S_"):
            taint_data["tainted"][i] = var[2:len(var)].replace("[0]", '')

    if taint_data["taint_label"] in taint_data["tainted"]:
        taint_data["tainted"].remove(taint_data["taint_label"])
    # print taint_info["tainted"]
    return taint_data


# Convert constraint analysis result to a JSON file
def format_constr_file(constr_file):
    with open(constr_file, "r") as in_file:
        file_lines = in_file.readlines()
    final_str = ""
    functions = []
    for line_num, line in enumerate(file_lines):
        line = line.rstrip('\n')
        if line_num == 0:
            line = line.strip('[')
        if line_num == len(file_lines) - 1:
            continue
        # Replace quote for printf function
        if "Call %s\\n" in line:
            quote_num = 0
            temp_str = list(line)
            for index, char in enumerate(line):
                if char == '\"':
                    quote_num += 1
                    if quote_num in [2, 3, 6, 7]:
                        temp_str[index] = ''
            line = "".join(temp_str)

        # Replace "func_end" with ',' except the last one
        if "func_end" in line:
            line = line.replace("func_end", '')
            final_str += line
            func = json.loads(final_str)
            if func["function"] not in ["zcl_Init", "zcl_event_loop"]:
                functions.append(func)
            final_str = ""
            continue

        # Replace "stmt_end" with ',' except the last one in the list
        if "stmt_end" in line and file_lines[line_num + 1].startswith("]}"):
            line = line.replace("stmt_end", '')
        elif "stmt_end" in line:
            line = line.replace("stmt_end", ',')
        final_str += line
    with open(constr_file + ".json", "w") as json_file:
        json.dump(functions, json_file, indent=4, ensure_ascii=False)
    return functions


def convert_hex_str(hex_str):
    """
    Convert received hex string to corresponding format for Z-Stack Execution.

    """
    seed = ""
    if hex_str not in string.printable or hex_str in string.whitespace:
        seed = seed + str(map(ord, hex_str)[0])
    else:
        seed = seed + hex_str
    return seed


def convert_seed(message, sep=""):
    seed = ""
    message = message.encode('ascii')
    for char in message:
        seed += convert_hex_str(char) + sep
    seed = seed.lstrip(' ').rstrip(' ')
    return seed


# Map taint message -> message field
# TODO: Improvement - saving the last matching record to reduce searching times
def search_field(index, message, seqs):
    field = ""
    for seq in seqs:
        data = convert_seed(seq["data"])
        if data == message:
            curr_lens = 0
            for i, field_len in enumerate(seq["length"]):
                curr_lens += field_len
                if curr_lens > index:
                    field = seq["fields"][i]["name"]
                    return field.encode()


def get_files(dir_path):
    files = []
    # all entries in the directory w/ stats
    data = (os.path.join(dir_path, fn) for fn in os.listdir(dir_path))
    data = ((os.stat(path), path) for path in data)

    # regular files, insert creation date
    data = ((stat[ST_CTIME], path)
            for stat, path in data if S_ISREG(stat[ST_MODE]))

    for path in sorted(data):
        files.append(path[1])
    return files


def update_annotation(message, inject=16847):
    # Get the pre-processing result of source code
    # which already includes Frama_C_dump_each function instrumentation (manually).
    with open("zcl_annot.i", "r") as source:
        contents = source.readlines()
    data = ""
    message = message.encode('ascii')
    for char in message:
        if char in string.ascii_letters:
            data += '\'' + char + '\''
        else:
            data += str(map(ord, char)[0])
        data += ','
    data = data.rstrip(',')
    print repr(data)
    logfile_name = "".join(m for m in data.replace('\'', '').split(','))
    # Inject taint label into source code and run taint analysis with Frama-C
    for index in range(0, len(message)):
        taint = "uint8 msg[] = {" + data + "};\n" + \
                "//@ taint msg[" + str(index) + "];\n" + \
                "pkt->cmd.Data = &msg;\npkt->cmd.DataLength = sizeof(msg);\n"
        # Manually inject taint to the target location.
        contents.insert(inject, taint)
        temp_file = "zcl_temp.i"
        with open(temp_file, "w") as ftemp:
            ftemp.write("".join(line for line in contents))

        # Run Frama-C for taint analysis from WSL
        framac_cmd = "wsl -e frama-c -machdep x86_32 -main zcl_ProcessMessageMSG -eva -eva-domains taint " \
                     "-eva-msg-key=d-taint -calldeps /home/mren/workspace/zigbfuzz/depenInfer/" + temp_file
        output = ""
        try:
            output = subprocess.check_output(framac_cmd, stderr=subprocess.STDOUT)
        except subprocess.CalledProcessError as e:
            print("Unexpected exception occured when running Frama-C!\n" + e.message)
            exit(1)

        if not output:
            print("No output from Frama-C execution!")
            exit(1)

        # Save analysis result to log file for further analysis
        log_file = "./logs/zcl_taint_[" + str(index) + "]_" + logfile_name + ".log"
        print log_file
        log = open(log_file, "w")
        log.write(output)
        log.close()
        # Clean up
        contents.pop(inject)
        os.remove(temp_file)
    return


if __name__ == '__main__':
    # Save input sequences
    with open("./input_sequences.json", "r") as seq_file:
        sequences = json.load(seq_file)

    if len(sys.argv) > 1 and sys.argv[1] == "-taint":
        # Run static taint analysis on ZCL for each sequence
        for seq in sequences:
            msg = seq["data"]
            update_annotation(msg)
    elif len(sys.argv) > 1 and sys.argv[1] == "-infer":
        # Get condition constraints in each function
        function_constrs = format_constr_file("./zcl_constraint_variables")

        # Iterate log files and get taint result
        log_files = get_files("./logs") + get_files("./manual_logs")
        for flog in log_files:
            trim_log(flog)
            taint_info = get_taint_info(flog)
            taint_index_start = taint_info["taint_label"].index('[') + 1
            taint_index_end = taint_info["taint_label"].index(']')
            taint_index = int(taint_info["taint_label"][taint_index_start:taint_index_end])
            taint_field = search_field(taint_index, taint_info["msg_value"], sequences)

            # Map the varaibles in each constraints to a message field
            for func in function_constrs:
                if func["function"] not in taint_info["func_calls"]:
                    continue
                for stmt in func["constraints"]:
                    if "field_deps" not in stmt.keys():
                        stmt["field_deps"] = []
                    if stmt["type"] == 'goto' or stmt["type"] == 'continue':
                        continue
                    vars = stmt["vars"]
                    for var in vars:
                        if isinstance(var, dict):
                            for v in var["vars"]:
                                if '->' in v:
                                    v = v.replace('->', '.')
                                if v in taint_info["tainted"] and taint_field not in stmt["field_deps"]:
                                    stmt["field_deps"].append(taint_field)
                                elif taint_field not in stmt["field_deps"]:
                                    root = v.split('.')[0]
                                    for t_var in taint_info["tainted"]:
                                        if t_var.startswith('S_'):
                                            t_var = t_var.replace("[0]", '')
                                            t_var = t_var[2:len(t_var)]
                                        if root == t_var:
                                            stmt["field_deps"].append(taint_field)
                                            break
                        else:
                            if '->' in var:
                                var = var.replace('->', '.')
                            if var in taint_info["tainted"] and taint_field not in stmt["field_deps"]:
                                stmt["field_deps"].append(taint_field)
                            elif taint_field not in stmt["field_deps"]:
                                root = var.split('.')[0]
                                for t_var in taint_info["tainted"]:
                                    if t_var.startswith('S_'):
                                        t_var = t_var.replace("[0]", '')
                                        t_var = t_var[2:len(t_var)]
                                    if root == t_var:
                                        stmt["field_deps"].append(taint_field)
                                        break
                    # print("%s: %s" % (stmt["stmt"], stmt["field_deps"]))

        with open("./zcl_constraint_deps.json", "w") as out_file:
            json.dump(function_constrs, out_file, ensure_ascii=False, indent=4)
    else:
        print("Please input the analysis options to be performed.\n"
              "\t-taint\tperform static taint analysis\n"
              "\t-infer\t perform constraint-field inference")
        exit(1)
