
import read, copy
from util import *
from logical_classes import *
from pdb import set_trace as bp
verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract_helper(self, fact):
        """Helper that removes a fact from a KB, as well as its support from associated facts/rules
        Args:
            fact (Fact)
        """
        if isinstance(fact, Fact):
            if not fact.supported_by:
                for f in fact.supports_facts:
                    for fr in f.supported_by:
                        if fact in fr:
                            f.supported_by.remove(fr)
                    self.kb_retract_helper(f) 
                for r in fact.supports_rules:
                    for fr in r.supported_by:
                        if fact in fr:
                            r.supported_by.remove(fr)
                    self.kb_retract_helper(r)
                # Remove fact itself from kb
                self.facts.remove(fact)
            else:
                if fact.asserted == True:
                    fact.asserted = False

        else:
            if not fact.supported_by:
                for f in fact.supports_facts:
                    for fr in f.supported_by:
                        if fact in fr:
                            f.supported_by.remove(fr)
                    self.kb_retract_helper(f) 

            # Iterate through fact's supported_rules
            # For every r in supported_rules, check if rule is supported by other things
            # If supported by other facts, keep it. If not, remove the rule
                for r in fact.supports_rules:
                    for fr in r.supported_by:
                        if fact in fr:
                            r.supported_by.remove(fr)
                    self.kb_retract_helper(r)
        
                self.rules.remove(fact)

            else:
                if fact.asserted == True:
                    fact.asserted = False    

    def kb_retract(self, fact_or_rule): 
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        # Must do the following:
        #   - Asserted and supported fact - change asserted to false
        #   - Asserted no support - remove it as support, recursively remove associated 
        #     ones that are not asserted and no longer have ANY support, and remove fact from KB
        #   - Supported no assert - do nothing (inferred)
        #   - Rule - nothing happens

        # Checking if arg is Fact
        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            fact = self._get_fact(fact_or_rule)
            self.kb_retract_helper(fact)
        # If not a Fact, do nothing
        else:
            #rule = self._get_rule(fact_or_rule)
            pass


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        
        bindings = match(fact.statement, rule.lhs[0])
        supported_by = [[fact, rule]]
        if bindings:
            new_statement = instantiate(rule.rhs, bindings)

            # Rule has 1 statement --> new Fact can be made
            if len(rule.lhs) == 1:
                new_fact = Fact(new_statement, supported_by)
                kb.kb_add(new_fact)
                new_fact = kb._get_fact(new_fact)
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                

            # Rule has multiple statements --> new Rule can be made with remaining LHS statements of old rule
            else:
                new_lhs = []
                for i in range(1, len(rule.lhs)):
                    new_lhs.append(instantiate(rule.lhs[i], bindings))

                new_rule = Rule([new_lhs, new_statement], supported_by)
                kb.kb_add(new_rule)
                new_rule = kb._get_rule(new_rule)
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)

