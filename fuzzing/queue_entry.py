import copy

from mutation import blocks


class QueueEntry:
    """
    The pending favored seed input
    """

    def __init__(self, mutant):
        self.last_check_depfields = None
        self.mutant_name = mutant._name  # the name of current mutant field
        self.value = mutant._value  # current value of mutant, will keep if favored
        self.was_fuzzed = False
        self.favored = False
        self.bitmap_size = 0  # number of bits set in bitmap
        self.exec_cksum = 0
        self.exec_us = 0  # execution time in millisecond
        self.current_mutant_index = mutant.mutant_index - 1  # mutation index of current primitive data
        self.interest_index = 0  # index in interesting values list
        self.trace_mini = None
        self.pending = True
        self.node_fields = []  # list of mutants when initialize the current node
        # list of mutants of rendered data, may different from node_fields,
        # e.g., change along with cmdId varies
        self.render_list = []
        self.render_index = 0
        self.original_render_index = 0

    def equal(self, other):
        if not isinstance(other, QueueEntry):
            raise Exception("Not a Node object!")
        if self.mutant_name == other.mutant_name and self.value == other.value \
                and self.node_fields == other.node_fields and self.bitmap_size == other.bitmap_size:
            return True
        return False

    def nodes_initialized(self, node_list):
        for index, node in enumerate(node_list):
            self.node_fields.append(copy.copy(node))
            self.render_list.append(copy.copy(node))
            if node.name == self.mutant_name:
                self.render_index = index
                self.original_render_index = index
        return

    def favored_render(self, fuzz_node):
        data = fuzz_node.render(self)
        render_list = []
        for i, item in enumerate(fuzz_node.render_list):
            render_list.append(copy.copy(item))
            if item._name == self.mutant_name:
                self.render_index = i
        self.render_list = render_list
        return data

    def favored_change(self, fuzz_node):
        """
        If current entry is replaced by a new favored entry but not completes its mutation, save current information
        for future resume.
        :param fuzz_node:
        :return:
        """
        self.pending = True
        self.was_fuzzed = True
        for index, item in enumerate(self.node_fields):
            if item.fuzzable:
                original = fuzz_node.names[item._name]
                if index > self.original_render_index:
                    item._mutant_index = original._mutant_index
                    item._value = original._value
        return

    def mutate(self, fuzz_data_logger, fuzz_node, infer_flag=False, depfields=None):
        mutated = False
        # Only mutate dependent field
        if infer_flag and depfields is not None:
            for field in depfields:
                if field == self.mutant_name:
                    self.last_check_depfields.remove(field)
                    # depfields.remove(field)
                    continue
                else:
                    for index, item in enumerate(self.render_list):
                        if item.name == field:
                            original = fuzz_node.names[item.name]
                            if original._skip_mutation:
                                original._skip_mutation = False
                            mutated = fuzz_node.mutate(field)
                            return mutated

        # Regular seed mutation
        if not self.pending and self.was_fuzzed:
            mutated = False
        elif self.pending and self.was_fuzzed:  # If current entry was fuzzed before but not completed
            self.pending = False
            self.was_fuzzed = False
            for index, item in enumerate(self.render_list):
                if item.fuzzable:
                    original = fuzz_node.names[item._name]
                    if index > self.render_index and fuzz_node.mutate(item._name):
                        mutated = True
                        if not isinstance(original, blocks.Block):
                            fuzz_node.mutant = original
                        break
                    else:
                        original._value = item._value
                        original._mutant_index = item._mutant_index
                        original._skip_mutation = True
        elif self.render_index == len(self.render_list) - 1:
            mutated = False
        else:
            for index, item in enumerate(self.render_list):
                if item.fuzzable:
                    original = fuzz_node.names[item._name]
                    if index > self.render_index and fuzz_node.mutate(item._name):
                        mutated = True
                        if not isinstance(original, blocks.Block):
                            fuzz_node.mutant = original
                        break
                    elif index < self.render_index:
                        original._skip_mutation = True
                        original._mutant_index = item._mutant_index
                        original._value = item._value
                    elif index == self.render_index:
                        original._skip_mutation = True
                        if original._fuzz_complete:
                            original._fuzz_complete = False
                        original._mutant_index = self.current_mutant_index
                        original._value = self.value
        return mutated

    def complete_mutate(self, fuzz_node):
        self.was_fuzzed = True
        self.pending = False
        for index, item in enumerate(self.node_fields):
            if item.fuzzable:
                original = fuzz_node.names[item._name]
                if index > self.original_render_index:
                    original.restart_mutation()
                    original._skip_mutation = False
                elif index < self.original_render_index:
                    original._skip_mutation = False
                    original._fuzz_complete = False
                else:
                    original._skip_mutation = False
                    original._fuzz_complete = False
                    original._mutant_index = self.current_mutant_index
                    original._value = self.value
        return
