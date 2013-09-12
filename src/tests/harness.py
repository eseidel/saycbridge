# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import itertools
import logging
import multiprocessing
import sys
import traceback
import unittest2

from core.call import Call
from core.callhistory import CallHistory, Vulnerability
from core.hand import Hand
from factory import BidderFactory
from third_party import outputcapture
from tests import test_sayc


_log = logging.getLogger(__name__)


# This is the simple version.  We'll need a fancier version of this function which can take a board.
def expectation_line(hand, call_history, expected_call=None):
    expected_call_string = expected_call.name if expected_call else "?"
    return "['%s', '%s', '%s']," % (
        hand.cdhs_dot_string(),
        expected_call_string,
        call_history.calls_string(),
    )


class CompiledTest(object):
    def __init__(self, group, hand, call_history, expected_call, parent_test=None):
        self.group = group
        self.hand = hand
        self.call_history = call_history
        self.expected_call = expected_call
        self.parent_test = parent_test

    @classmethod
    def from_expectation_tuple_in_group(cls, expectation, test_group):
        hand_string = expectation[0]
        assert '.' in hand_string, "_split_expectation expectes C.D.H.S formatted hands, missing '.': %s" % hand_string
        expected_call = Call.from_string(expectation[1])
        history_string = expectation[2] if len(expectation) > 2 else ""
        vulnerability_string = expectation[3] if len(expectation) > 3 else None
        hand = Hand.from_cdhs_string(hand_string)
        call_history = CallHistory.from_string(history_string, vulnerability_string=vulnerability_string)
        return cls(test_group, hand, call_history, expected_call)

    @property
    def identifier(self):
        # FIXME: Our "have we run this" check would be more powerful if we used a combinatics based identifier for the hands.
        return "%s-%s" % (self.hand.cdhs_dot_string(), self.call_history.identifier)

    @property
    def subtest_string(self):
        if self.parent_test:
            return " (subtest of %s)" % self.parent_test.call_history.calls_string()
        return ""

    @property
    def test_string(self):
        return "%s, history: %s%s" % (self.hand.pretty_one_line(), self.call_history.calls_string(), self.subtest_string)

    @property
    def subtests(self):
        subtests = []
        partial_history = self.call_history
        while len(partial_history.calls) >= 4:
            expected_call = partial_history.calls[-4]
            partial_history = partial_history.copy_with_partial_history(-4)
            subtests.append(CompiledTest(self.group, self.hand, partial_history, expected_call, self))
        return subtests


class TestGroup(object):
    def __init__(self, name):
        self.name = name
        self._seen_expectations = {}
        self.tests = []

    def add_test(self, test):
        # Sanity check to make sure we're not running a test twice.
        test_identifier = test.identifier
        previous_call = self._seen_expectations.get(test_identifier)
        if previous_call:
            if previous_call != test.expected_call:
                _log.error("Conflicting expectations for %s, %s != %s" % (test_identifier, previous_call, test.expected_call))
            elif not test.parent_test:
                 _log.debug("%s is an explicit duplicate of an earlier test." % test_identifier)
            else:
                _log.debug("Ignoring dupliate subtest %s" % test_identifier)
            return
        self._seen_expectations[test_identifier] = test.expected_call
        self.tests.append(test)

    def add_expectation_line(self, expectation):
        try:
            test = CompiledTest.from_expectation_tuple_in_group(expectation, self)
        except:
            print "Exception compiling: %s in group %s" % (expectation, self.name)
            raise
        self.add_test(test)
        for test in test.subtests:
            self.add_test(test)

    def add_expectation_lines(self, expectation_lines):
        for expectation in expectation_lines:
            self.add_expectation_line(expectation)


class ResultsAggregator(object):
    def __init__(self, groups):
        self.groups = groups
        self._results_count_by_group = { group.name: 0 for group in self.groups }
        self._results_by_identifier = {}
        self._group_has_printed = [False for group in self.groups]
        self._total_failures = 0

    def _is_complete(self, group):
        return self._results_count_by_group.get(group.name) == len(group.tests)

    def _print_completed_groups(self):
        for index, has_printed in enumerate(self._group_has_printed):
            if has_printed == True:
                continue
            group = self.groups[index]
            if not self._is_complete(group):
                return
            self._print_group_summary(group)
            self._group_has_printed[index] = True

    def _print_group_summary(self, group):
        fail_count = 0
        print "%s:" % group.name
        for test in group.tests:
            result = self._results_by_identifier[test.identifier]
            result.print_captured_logs()

            if result.exc_str:
                _log.error("Exception during find_call_for %s %s: %s" % (test.hand.pretty_one_line(), test.call_history.calls_string(), result.call))
                _log.error(result.exc_str)
                raise StopIteration

            if result.call and result.call == test.expected_call:
                _log.info("PASS: %s for %s" % (test.expected_call, test.test_string))
            else:
                fail_count += 1
                print "FAIL: %s (expected %s) for %s" % (result.call, test.expected_call, test.test_string)

        # FIXME: We don't need to update _total_failures here.
        self._total_failures += fail_count
        print "Pass %s of %s hands" % (len(group.tests) - fail_count, len(group.tests))
        print

    def add_results_callback(self, results):
        for result in results:
            # FIXME: Instead of warning, we should assert here, and we should fix
            # duplicated detection to be global, instead of per TestGroup.
            # existing_result = self._results_by_identifier.get(result.test.identifier)
            # if existing_result:
            #     print "WARNING: Got duplicate result (%s, %s) %s" % (existing_result.call, result.call, result.test.test_string)
            self._results_by_identifier[result.test.identifier] = result
            self._results_count_by_group[result.test.group.name] += 1
        self._print_completed_groups()

    # These were explicitly tested and matched some hand.
    @property
    def called_rule_names(self):
        rule_names = map(lambda result: result.rule_name, self._results_by_identifier.values())
        return set(map(str, filter(None, rule_names)))

    # These were tested via interpretation of a call_history.
    @property
    def interpreted_rule_names(self):
        rule_name_tuples = map(lambda result: result.last_three_rule_names, self._results_by_identifier.values())
        # result.last_three_rule_names can be None.
        rule_name_tuples = filter(None, rule_name_tuples)
        rule_names = itertools.chain.from_iterable(rule_name_tuples)
        return set(map(str, filter(None, rule_names)))

    def print_summary(self):
        total_tests = len(self._results_by_identifier)
        total_pass = total_tests - self._total_failures
        percent = 100 * total_pass / total_tests if total_tests else 0
        print "Pass %s (%.1f%%) of %s total hands" % (total_pass, percent, total_tests)


# Pickle gets mad at us if we make this a member or even static function.
# This call is executed in a different process when running tests in parallel.
def _run_test(test):
    # FIXME: There is no need to lookup the bidder every time.
    bidder = BidderFactory.default_bidder()
    result = TestResult()
    result.test = test
    # FIXME: OutputCapture captures logging channels as well which is probably a waste.
    output = outputcapture.OutputCapture()
    stdout, stderr = output.capture_output()
    try:
        call_selection = bidder.call_selection_for(test.hand, test.call_history)
        if call_selection:
            result.call = call_selection.call
            result.rule_name = str(call_selection.rule)
            result.fill_last_three_rule_names(call_selection)

            if result.last_three_rule_names and result.last_three_rule_names[-2] is None:
                print "WARNING: Failed to interpret partner's last bid: %s" % test.call_history.copy_with_partial_history(-2)

    except Exception:
        result.exc_str = ''.join(traceback.format_exception(*sys.exc_info()))
    output.restore_output()
    result.save_captured_logs(stdout, stderr)
    return result


class TestHarness(unittest2.TestCase):
    use_multi_process = True
    test_shard_size = 10

    def __init__(self, *args, **kwargs):
        super(TestHarness, self).__init__(*args, **kwargs)
        self.groups = []
        self.results = None

    def collect_test_groups(self):
        # sorted happens to "just work" here since tuples are compared in item order.
        # Since we know we don't have any duplicate keys, the values will never be compared.
        for group_name, expectations_list in sorted(test_sayc.sayc_expectations.items()):
            group = TestGroup(group_name)
            group.add_expectation_lines(expectations_list)
            self.groups.append(group)

    def run_tests_single_process(self):
        # This follows the same logic-flow as the multi-process code, yet stays single threaded.
        all_tests = list(itertools.chain.from_iterable(group.tests for group in self.groups))
        for x in range(0, len(all_tests), self.test_shard_size):
            shard = all_tests[x : x + self.test_shard_size]
            results = map(_run_test, shard)
            self.results.add_results_callback(results)

    def run_tests_multi_process(self):
        all_tests = list(itertools.chain.from_iterable(group.tests for group in self.groups))
        pool = multiprocessing.Pool()
        # FIXME: outstanding_jobs + map_async is a workaround for http://bugs.python.org/issue8296 (only fixed in python 3)
        outstanding_jobs = []
        for x in range(0, len(all_tests), self.test_shard_size):
            results = pool.map_async(
                _run_test,
                all_tests[x : x + self.test_shard_size],
                self.test_shard_size,
                self.results.add_results_callback
            )
            outstanding_jobs.append(results)
        pool.close()

        # Calling pool.join() won't handle KeyboardInterrupts, so we do a timed wait
        # on each individual results object.
        while outstanding_jobs:
            outstanding_jobs.pop(0).wait(0xFFFF)

        pool.terminate()

    def _print_coverage_summary(self):
        # FIXME: This need not depend on z3 specifically.
        try:
            all_rules = BidderFactory.default_bidder().system.rules
        except:
            print "Ignoring coverage summary, failed to find rules."
            return

        all_rule_names = set(map(str, all_rules))

        # Don't expect to see rules which are marked "requires_planning".
        non_planned_rules = filter(lambda rule: not rule.requires_planning, all_rules)
        non_planned_rule_names = set(map(str, non_planned_rules))
        called_rule_names = self.results.called_rule_names
        planned_rule_count = len(all_rule_names) - len(non_planned_rule_names)
        print "Tested call generation of %s rules of %s total (excluding %s requires_planning rules)." % (len(called_rule_names), len(non_planned_rule_names), planned_rule_count)
        uncalled_rule_names = non_planned_rule_names - called_rule_names
        if uncalled_rule_names:
            print "Never selected call from:"
            print "\n".join(sorted(uncalled_rule_names))

        interpreted_rule_names = self.results.interpreted_rule_names
        print "\nTested interpretation of %s rules of %s total." % (len(interpreted_rule_names), len(all_rule_names))
        uninterpreted_rule_names = all_rule_names - interpreted_rule_names
        # FIXME: We should print these, but we have too many right now!
        # if uninterpreted_rule_names:
        #     print "Never interpreted call with:"
        #     print "\n".join(sorted(uninterpreted_rule_names))

        never_tested_rule_names = uncalled_rule_names & uninterpreted_rule_names
        if uninterpreted_rule_names:
            print "\n%s rules were never used for either bidding or interpretation:" % len(never_tested_rule_names)
            print "\n".join(sorted(never_tested_rule_names))

    def test_main(self):
        self.collect_test_groups()
        self.results = ResultsAggregator(self.groups)
        if self.use_multi_process:
            self.run_tests_multi_process()
        else:
            self.run_tests_single_process()
        self.results.print_summary()
        print
        self._print_coverage_summary()


class TestResult(object):
    def __init__(self):
        self.test = None
        self.call = None
        self.rule_name = None
        # We only bother to store the last 3, as the subtest system will have handled all calls before that.
        self.last_three_rule_names = None
        self.exc_str = None
        self.stdout = None
        self.stderr = None

    def fill_last_three_rule_names(self, call_selection):
        # FIXME: This is kinda an ugly z3b-dependant hack.
        if not hasattr(call_selection, "rule_selector"):
            return
        from z3b.model import positions
        # These are in call-order, so we'd access partner's via names[-2].
        last_three_positions = (positions.LHO, positions.Partner, positions.RHO)
        # This history is prior to the call_selection's call.
        history = call_selection.rule_selector.history
        self.last_three_rule_names = map(str, map(history.rule_for_last_call, last_three_positions))

    def save_captured_logs(self, stdout, stderr):
        self.stdout = stdout.getvalue()
        self.stderr = stderr.getvalue()

    def print_captured_logs(self):
        if self.stderr:
            sys.stderr.write(self.stderr)
        if self.stdout:
            sys.stdout.write(self.stdout)
