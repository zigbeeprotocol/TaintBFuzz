import copy
import json
import re
import socket
import coverage
import lib_zstack_constants as constant
from mutation import helpers, blocks

# Get the succeeding blocks of the given block
from queue_entry import QueueEntry


def get_succs(block, funct_cfg):
    for b in funct_cfg["block_list"]:
        if block == b["block_number"]:
            return b["succs"]
    return []


# Get the statements of the given block
def get_statements(node, funct_cfg):
    for b in funct_cfg["block_list"]:
        if node == b["block_number"]:
            return b["statements"]
    return []


def search_constraint_in_dependency(func_name, dependency):
    for f in dependency:
        if f["function"] == func_name:
            return f["constraints"]  # TODO: Fix typo in depenInfer codes
    return []


def get_dependency(func_name, statements, dependency):
    constraints = search_constraint_in_dependency(func_name, dependency)
    fields = []
    for constr in constraints:
        if constr["stmt"].split()[1] in statements and "field_deps" in constr.keys():
            fields.extend(constr["field_deps"])
    return fields


def search_function_in_cfg(cfg, name):
    """
    Find a specific function in CFG
    :param cfg: the CFG data of ZCL module
    :param name: function name
    :return: return the found function object
    """
    func_list = cfg.get('function_list')
    for function in func_list:
        if function.get('name') == name:
            return function
    return None


def unlikely(exp):
    if not not exp == 0:
        return False
    return True


def likely(exp):
    if not not exp == 1:
        return True
    return False


def FF(value):
    return 0xff << (value << 3)


def checksum(trace_bit):
    return hash(tuple(trace_bit))


# Address received execution status
unsuccessful_status = ["Process Failed!"]
for stat in range(1, 9):
    unsuccessful_status.append(str(stat))


# Update coverage information after each test case
def check_execution(target, fuzz_data_logger, session, sock, *args, **kwargs):
    session_coverage = session.coverage

    # Save the initial execution call stack
    if not session_coverage.curr_callstack:
        with open(constant.call_stack_file, "r") as callstack:
            session_coverage.curr_callstack = json.load(callstack, encoding="ascii")

    # Parse and calculate coverage information
    session_coverage.parse_coverage_result()
    # Check and update bitmap if it has new bits
    hnb = has_new_bit(session_coverage, session_coverage.virgin_bits)
    save_if_interest(session, hnb)

    # Check target execution status
    status = session.last_recv
    if status is not None and "Process Failed!" in status:
        session_coverage.total_crash += 1
        find_unique_crash(session_coverage, status)
    elif status == "Server Error!\n":
        # Server Error: no error message received
        session_coverage.total_crash += 1
        session_coverage.uni_crash += 1
    # else:
    #     stat_index = int(status)
    #     session_coverage.status_hits[stat_index] += 1

    show_stats(session, fuzz_data_logger)

    if hnb == 2:  # Has new coverage
        # Check if previous inferred uncovered branch is covered or not
        check_infer_cover_state(session, hnb)
        session_coverage.last_coverage['test_case'] = session.total_mutant_index
        session_coverage.last_coverage['coverage'] = session_coverage.bitmap_state['edge']
        # select_seed(fuzz_data_logger, session, session.fuzz_node)
    return


def find_unique_crash(curr_coverage, stack):
    start = stack.find("Call Stack:")
    if start != -1:  # Receive call stack information
        call_stack = stack[start + len("Call Stack:\r\n"):].split("\r\n")
        mem_address = []
        memory_ptn = "^0x[0-9a-zA-Z]+"
        # Extract memory address from call stack for hashing
        for line in call_stack:
            split_line = line.split(" ")
            for data in split_line:
                if re.search(memory_ptn, data):
                    mem_address.append(data)
                    break
        stack_hash = checksum(mem_address)
        if stack_hash not in curr_coverage.crash_stack:
            curr_coverage.crash_stack[stack_hash] = mem_address
            curr_coverage.uni_crash += 1
    else:
        # No call stack information returned from target, we just hash the whole stack information
        stack_hash = checksum(stack)
        if stack_hash not in curr_coverage.crash_stack:
            curr_coverage.crash_stack[stack_hash] = stack
            curr_coverage.uni_crash += 1
    return


def save_if_interest(session, has_new_bits):
    current_cov = session.coverage
    current_mutant = session.fuzz_node.mutant
    favored_list = current_cov.interest
    # Only insert node when it has covered new tuples
    if has_new_bits == 2:
        mutant = QueueEntry(current_mutant)
        mutant.exec_cksum = checksum(current_cov.trace_bits)
        mutant.favored = True
        mutant.exec_us = current_cov.current_exec_us
        mutant.bitmap_size = count_bits(current_cov.trace_bits)
        mutant.nodes_initialized(session.fuzz_node.render_list)
        mutant.exec_path = current_cov.curr_callstack

        redundant = False
        for favored in favored_list:
            if mutant.equal(favored):
                return

        last_field = None
        for index in range(len(mutant.node_fields) - 1, -1, -1):
            item = mutant.node_fields[index]
            if item.fuzzable:
                last_field = item._name
                break

        if not redundant and last_field != mutant.mutant_name:
            mutant._render = session.last_send
            mutant.interest_index = len(favored_list)
            favored_list.append(mutant)
            current_cov.new_favored = True
            current_cov.pending_favored += 1
            # if mutant.interest_index == 0:
            #     current_cov.current_favored = mutant
    return


# Select and render the seed which has the highest bitmap size
def select_seed(target, fuzz_data_logger, session, node, *args, **kwargs):
    curr_coverage = session.coverage
    data = b""

    if session.coverage.new_favored:
        cull_favored(session.infer_flag, session.fuzz_node, curr_coverage)

    if curr_coverage.pending_favored:
        favored = curr_coverage.top_rated[-1]
        if curr_coverage.current_favored is None:
            curr_coverage.current_favored = favored
        elif not curr_coverage.current_favored.equal(favored):
            prev_favored = curr_coverage.current_favored
            prev_favored.favored_change(node)
            curr_coverage.current_favored = favored
            favored.pending = True
        else:
            data = curr_coverage.current_favored.favored_render(session.fuzz_node)
            fuzz_data_logger.open_test_step("Current pending favored mutate: %s:%s" %
                                            (curr_coverage.current_favored.mutant_name,
                                             repr(curr_coverage.current_favored.value)))
            return data

        if favored.pending and not favored.was_fuzzed:
            favored.pending = False
            data = favored.favored_render(node)
            node.mutant = copy.copy(node.names[favored.mutant_name])
        elif not favored.was_fuzzed:
            data = favored.favored_render(node)
    else:
        curr_coverage.current_favored = None
        data = node.render()

    return data


def cull_favored(infer_flag, fuzz_node, cur_coverage):
    favored_queue = cur_coverage.interest
    cur_coverage.new_favored = False
    if len(favored_queue) == 0:
        cur_coverage.pending_favored = 0
        cur_coverage.current_favored = None
        cur_coverage.top_rated = []
        return
    elif len(favored_queue) == 1:
        cur_coverage.top_rated = copy.copy(favored_queue)
        cur_coverage.current_favored = copy.copy(favored_queue[0])
        cur_coverage.pending_favored = 1
        return

    del cur_coverage.top_rated[:]
    # Remove fuzzed favored for sorting
    favored_queue = []
    for favored in cur_coverage.interest:
        if not favored.was_fuzzed:
            # reset_favored(fuzz_node, favored)
            favored_queue.append(favored)

    def sort_favored(x):  # Sort seed based on its covered edges * field length
        return x.bitmap_size * (len(x.node_fields) * -1)

    if not infer_flag:
        cur_coverage.top_rated = sorted(favored_queue, key=sort_favored)
    cur_coverage.pending_favored = len(cur_coverage.top_rated)
    return


def reset_favored(fuzz_node, favored):
    favored.render_list = favored.node_fields
    favored.render_index = favored.original_render_index
    node_names = [x.name for x in favored.node_fields]
    for node in fuzz_node.names:
        if node in node_names:
            node_index = node_names.index(node)
            fuzz_node.names[node] = copy.copy(favored.node_fields[node_index])
        else:
            fuzz_node.names[node].restart_mutation()
    return


def restart_callback(target, fuzz_data_logger, session, sock):
    try:
        data = target.recv(constant.buffer_size)
        if not data:
            raise
    except socket.error:
        session.fuzz_node.reset()
        target.close()
        exit(1)
    return


def has_new_bit(curr_coverage, virgin_map):
    current = curr_coverage.trace_bits
    virgin = virgin_map
    iterate = constant.map_size
    index = 0
    ret = 0
    current_non_255_bits = count_non_255_bits(virgin)
    while iterate > 0:
        if current[index]:
            virgin[index] &= ~current[index]
            ret = 1
        index += 1
        iterate -= 1
    new_non_255_bits = count_non_255_bits(virgin)
    if current_non_255_bits != new_non_255_bits:
        ret = 2
    return ret


# Set up bitmap when the session start. Only execute one time.
def setup_bitmap(session):
    if not hasattr(session, 'coverage') or session.coverage is None:
        session.coverage = coverage.Coverage()
        session.coverage.init_count_class16()
    return


# Calculate bitmap coverage
def show_stats(session, fuzz_data_logger):
    curr_coverage = session.coverage
    edge_bits, hit_total = count_non_255_bits(curr_coverage.virgin_bits)
    stmt_bits = count_bits(curr_coverage.statement_bits)
    statement = (float(stmt_bits) * 100) / curr_coverage.total_statement
    edge = (float(edge_bits) * 100) / curr_coverage.total_edge
    curr_coverage.bitmap_state['statement'] = statement
    curr_coverage.bitmap_state['edge'] = edge

    # Log necessary information for analysis
    hit_stmt = []
    for index, bit in enumerate(curr_coverage.statement_bits):
        if bit:
            hit_stmt.append(index)
    curr_coverage.hit_stmt_index = sorted(hit_stmt)
    hit_edge = []
    for index, bit in enumerate(curr_coverage.virgin_bits):
        if bit != 255:
            hit_edge.append(index)
    curr_coverage.hit_edge_index = sorted(hit_edge)

    fuzz_data_logger.log_info(
        "Execution time: %d; Total Crash: %d (%d unique); Statement coverage: %d (%.2f%%); Edge coverage: %d (%.2f%%)" %
        (curr_coverage.current_exec_us, curr_coverage.total_crash, curr_coverage.uni_crash, stmt_bits, statement, edge_bits, edge)
    )
    coverage_stat = open(constant.coverage_stat_dir + "coverage_stat_" + curr_coverage.init_timestamp + ".txt", "a")
    coverage_stat.write(
        "\nMessage%d: %s\r\nTime: %s\n\rFavored seed:%d\r\nHit functions:%d\r\nTotal Crash: %d (%d unique); Statement "
        "coverage: %d (%.2f%%); Edge coverage: %d (%.2f%%)\r\n "
        "Hit statements:%s\r\nHit edges:%s\r\nBlock Trace:%s\r\n" %
        (session.total_mutant_index, repr(session.last_send), helpers.get_time_stamp(), len(curr_coverage.interest),
         len(curr_coverage.hit_function), curr_coverage.total_crash, curr_coverage.uni_crash, stmt_bits, statement,
         edge_bits, edge, curr_coverage.hit_stmt_index, hit_edge, json.dumps(curr_coverage.trace)))
    coverage_stat.write("\nCall Stack Trace:%s\r\n" % json.dumps(curr_coverage.curr_callstack))
    coverage_stat.close()
    return


# Count bits set in a bitmap. Non zero value.
def count_bits(bitmap):
    count = 0
    for bit in bitmap:
        if bit:
            count += 1
    return count


def count_non_255_bits(bitmap):
    count = 0
    bits_total = 0
    for bit in bitmap:
        if bit != 255:
            count += 1
            bits_total += (255 - bit)
    return count, bits_total


def check_field_dep(session, fuzz_data_logger, dependency=None):
    curr_path = session.coverage.curr_callstack
    statements = []
    for func in curr_path:
        if hasattr(func, "stmt_trace"):
            statements.extend(func["stmt_trace"])
    curr_dep_field = []

    # Initial state
    if not hasattr(session, "curr_dep_field_index"):
        session.curr_dep_func_index = len(curr_path) - 1
        session.last_dep_path = copy.copy(curr_path)
        session.last_path_hash = checksum(statements)
    elif checksum(statements) != session.last_path_hash:
        session.curr_dep_func_index = len(curr_path) - 1
        session.last_dep_path = copy.copy(curr_path)
        session.last_path_hash = checksum(statements)

    # Backtracking the called functions in the exec path from the last one
    while session.curr_dep_func_index >= 0:
        curr_function = curr_path[session.curr_dep_func_index]
        cfg_dict = session.coverage.cfg_dict
        bb_index = len(curr_function["bb_trace"]) - 1  # The last block is alwarys #1 that exits the function.
        uncovered = False
        bb_for_dep_search = None
        cfg_func = search_function_in_cfg(cfg_dict, curr_function["function"])
        while bb_index >= 0:  # backtracking from the last basic block
            bb_parent = curr_function["bb_trace"][bb_index - 1]
            bb_for_dep_search = cfg_func["block_list"][int(bb_parent) - 1]
            for succ in bb_for_dep_search["succs"]:
                if succ == 1:
                    break
                if cfg_func["block_list"][succ - 1]["status"] == 0:
                    uncovered = True
                    session.infer_uncovered = cfg_func["block_list"][succ - 1]["statements"]
                    break
            if uncovered:
                break
            bb_index -= 1
        # The current function has uncovered branch
        if uncovered and bb_for_dep_search is not None:
            for dep_func in dependency:
                if curr_function["function"] == dep_func["function"]:
                    condition_ln = bb_for_dep_search["statements"][-1]
                    for constr in dep_func["constraints"]:
                        if str(condition_ln) in constr["stmt"]:
                            for dep in constr["field_deps"]:
                                if dep not in curr_dep_field:
                                    curr_dep_field.append(dep)
                    break
            if len(curr_dep_field) != 0:
                fuzz_data_logger.open_test_step(
                    "Check fields dependency on function {0}".format(curr_function["function"]))
                break
        # All branches in current function have been covered, then backtrace to the next function in the path
        session.curr_dep_func_index -= 1

    return curr_dep_field


def compare_callstack(prev_stack, new_stack):
    # If the last called function is the same, then we think no change
    if len(prev_stack) == len(new_stack) and prev_stack[-1]["function"] == new_stack[-1]["function"]:
        return True
    for old in prev_stack[:-1]:
        for new in new_stack:
            if old["function"] != new["function"]:
                # print old["function"], new["function"]
                return False
    return True


# If the previous inferred uncovered branch has been covered in the new execution,
# then we give control back to original fuzzing
def check_infer_cover_state(session, new_bit):
    curr_coverage = session.coverage
    curr_path = curr_coverage.curr_callstack
    logger = session._fuzz_data_logger
    if new_bit == 2 and hasattr(session, "infer_uncovered") and len(session.infer_uncovered) != 0:
        stmt_covered = all(x in curr_coverage.hit_stmt_index for x in session.infer_uncovered)
        callstack_same = compare_callstack(session.last_dep_path, curr_path)
        # Case 1: Call stack fully changed and not cover the inferred branch
        if not callstack_same and not stmt_covered:
            # If there is pending favored seed, revert its preceding fields
            if curr_coverage.current_favored and len(curr_coverage.current_favored.last_check_depfields) != 0:
                for i, item in enumerate(curr_coverage.current_favored.node_fields):
                    if item._name in curr_coverage.current_favored.last_check_depfields:
                        original = session.fuzz_node.names[item._name]
                        original._mutant_index += 1
                        if i < curr_coverage.current_favored.render_index:
                            original._skip_mutation = True
                            original._mutant_index = item._mutant_index
                            original._value = item._value
                        elif i == curr_coverage.current_favored.render_index:
                            original._skip_mutation = True
                            original._mutant_index = item._mutant_index - 1
                            original._value = item._value
                        else:
                            session.infer_flag = True
                            # Case 1: Try the next candidate value if possible
                            if not original._fuzz_complete:
                                original._mutant_index += 1
                            # Case 2: No more mutation and not cover the inferred branch. Try next dep field.
                            else:
                                original.restart_mutation()
                                curr_coverage.current_favored.last_check_depfields.remove(item._name)
            #   for i, field in enumerate(curr_coverage.current_favored.node_fields):
            #     if field in session.last_check_depfields and i <= curr_coverage.current_favored.render_index:
            #         original = session.fuzz_node.names[field]
            #         original._mutant_index = field._mutant_index
            #         original._value = field._value
            #     elif field in session.last_check_depfields and i > curr_coverage.current_favored.render_index:
            #         session.infer_flag = True
            #         original = session.fuzz_node.names[field]
            #         # Case 1: Try the next candidate value if possible
            #         if not original._fuzz_complete:
            #             original._mutant_index += 1
            #         # Case 2: No more mutation and not cover the inferred branch.
            #         # Try the next dependent field
            #         else:
            #             original.restart_mutation()
            #             session.last_check_depfields.pop(i)
            #             new_mutant = session.fuzz_node.names[session.last_check_depfields[0]]
            #             session.fuzz_node.mutant = new_mutant
            #             logger.log_info("Mutate next dependent field:%s" % new_mutant._name)
            else:
                session.infer_flag = True
                original = session.fuzz_node.mutant
                for i, field in enumerate(session.last_check_depfields):
                    if original._name == field:
                        # Case 1: Try the next candidate value if possible
                        if not original._fuzz_complete:
                            original._mutant_index += 1
                        # Case 2: No more mutation and not cover the inferred branch.
                        # Try the next dependent field
                        else:
                            original.restart_mutation()
                            session.last_check_depfields.pop(i)
                            new_mutant = session.fuzz_node.names[session.last_check_depfields[0]]
                            session.fuzz_node.mutant = new_mutant
                            logger.log_info("Mutate next dependent field:%s" % new_mutant._name)
        elif callstack_same and not stmt_covered:
            # Case 2: Call stack is same but not cover the inferred branch. Continue for infer-guided mutation.
            session.infer_flag = True
        else:
            # Case 3: Call stack changed but cover the inferred branch
            # Case 4: Call stack same and cover the inferred branch (Ideal state)
            if session.coverage.current_favored is not None:
                session.fuzz_node.mutant = copy.copy(
                    session.fuzz_node.names[curr_coverage.current_favored.mutant_name])
                if len(curr_coverage.current_favored.last_check_depfields) != 0:
                    for f in curr_coverage.current_favored.node_fields:
                        if f._name in curr_coverage.current_favored.last_check_depfields:
                            session.fuzz_node.names[f._name] = copy.copy(f)
                    curr_coverage.current_favored.last_check_depfields = []
                logger.log_info(
                    "Cover inferred branch. Switch back to the current favored mutant:%s" % session.coverage.current_favored.mutant_name)
            elif hasattr(session, "mutant_before_infer"):
                session.fuzz_node.mutant = copy.copy(session.mutant_before_infer)
                logger.log_info(
                    "Cover inferred branch. Switch back to regular fuzzing on mutant:%s" % session.mutant_before_infer._name)

            session.infer_flag = False
            session.infer_uncovered = []
            session.curr_dep_func_index = 0
            session.last_dep_path = None
            session.last_path_hash = 0
    return


def mutate_with_inference(fuzz_data_logger, fuzz_node, depfields, infer_flag=False):
    mutated = False
    # Only mutate dependent field
    if infer_flag and depfields is not None:
        for field in depfields:
            if field == fuzz_node.mutant.name:
                original = fuzz_node.names[fuzz_node.mutant.name]
                if original._skip_mutation:
                    original._skip_mutation = False
                mutated = original.mutate()
                if mutated:
                    if not isinstance(original, blocks.Block):
                        fuzz_node.mutant = original
                    fuzz_data_logger.log_info("Mutate dependent field:%s" % field)
                    break
                if original._fuzz_complete:
                    original.restart_mutation()
                    # depfields.pop(0)
                    fuzz_node.last_check_depfields.remove(field)
                    mutated = True
            else:
                for index, item in enumerate(fuzz_node.render_list):
                    if item._name == field and item.fuzzable:
                        original = fuzz_node.names[item._name]
                        if original._skip_mutation:
                            original._skip_mutation = False
                        mutated = original.mutate()
                        if mutated:
                            if not isinstance(original, blocks.Block):
                                fuzz_node.mutant = original
                            fuzz_data_logger.log_info("Mutate dependent field:%s" % item._name)
                            break
                        if original._fuzz_complete:
                            original.restart_mutation()
                            # depfields.pop(0)
                            fuzz_node.last_check_depfields.remove(field)
                            mutated = True
                            break
                if mutated:
                    break
        return mutated
