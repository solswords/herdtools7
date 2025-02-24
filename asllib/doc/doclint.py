#!/usr/bin/python3

import os, sys, fnmatch
from extended_macros import apply_all_macros, get_latex_sources
import re
from dataclasses import dataclass
from typing import List, Set
import argparse

cli_parser = argparse.ArgumentParser(prog="ASL Reference Linter")
cli_parser.add_argument(
    "-m",
    "--macros",
    help="Rewrites *.tex files with extended macros",
    action="store_true",
)

num_rules = 0

def read_file_lines(filename: str) -> List[str]:
    with open(filename, "r", encoding="utf-8") as file:
        return file.readlines()


def read_file_str(filename: str) -> List[str]:
    with open(filename, "r", encoding="utf-8") as file:
        return file.read()


def extract_labels_from_line(line: str, left_delim: str, labels: set[str]):
    r"""
    Adds all labels found in `line` into `labels`. A label starts with the
    sub-string given by `left_delim` and ends with the substring `}`.
    """
    right_delim = "}"
    label_pos: int = 0
    while True:
        label_pos: int = line.find(left_delim, label_pos)
        if label_pos == -1:
            return
        right_brace_pos: int = line.find(right_delim, label_pos)
        if right_brace_pos == -1:
            return
        label = line[label_pos + len(left_delim) : right_brace_pos]
        labels.add(label)
        label_pos = right_brace_pos + 1


def check_hyperlinks_and_hypertargets(latex_files: list[str]):
    r"""
    Checks whether all labels defined in `\hyperlink` definitions match
    labels defined in `\hypertarget` definitions, print the mismatches
    to the console.
    """
    hyperlink_labels: set[str] = set()
    hypertarget_labels: set[str] = set()
    for latex_source in latex_files:
        for line in read_file_str(latex_source):
            extract_labels_from_line(line, "\\hyperlink{", hyperlink_labels)
            extract_labels_from_line(line, "\\hypertarget{", hypertarget_labels)
    num_errors = 0
    missing_hypertargets = hyperlink_labels.difference(hypertarget_labels)
    if missing_hypertargets:
        num_missing_hypertargets = len(missing_hypertargets)
        num_errors += num_missing_hypertargets
        print(
            f"ERROR: found {num_missing_hypertargets} hyperlinks without \
              matching hypertargets: ",
            file=sys.stderr,
        )
        for label in missing_hypertargets:
            print(label, file=sys.stderr)

    missing_hyperlinks = hypertarget_labels.difference(hyperlink_labels)
    if not missing_hyperlinks == set():
        num_missing_hyperlinks = len(missing_hyperlinks)
        num_errors += num_missing_hyperlinks
        print(
            f"ERROR: found {num_missing_hyperlinks} hypertargets without\
               matching hyperlinks: ",
            file=sys.stderr,
        )
        for label in missing_hyperlinks:
            print(label, file=sys.stderr)

    return num_errors


def check_undefined_references_and_multiply_defined_labels():
    r"""
    Checks whether the LaTeX compiler found any undefined labels
    or multiply-defined labels.
    """
    num_errors = 0
    log_str = read_file_str("./ASLReference.log")
    if "LaTeX Warning: There were undefined references." in log_str:
        print(
            f"ERROR: There are undefined references (see ./ASLReference.log)",
            file=sys.stderr,
        )
        num_errors += 1
    if "LaTeX Warning: There were multiply-defined labels." in log_str:
        print(
            f"ERROR: There are multiply-defined labels (see ./ASLReference.log)",
            file=sys.stderr,
        )
        num_errors += 1
    if "destination with the same identifier" in log_str:
        print(
            f"ERROR: There are multiply-defined \\hypertarget labels \
                (see 'destination with the same identifier' in \
                ./ASLReference.log)",
            file=sys.stderr,
        )
        num_errors += 1
    return num_errors


def check_tododefines(latex_files: list[str]):
    r"""
    Checks that there are no more than the expected number of \tododefine
    instances.
    """
    MAX_TODODEFINE_INSTANCES = 7
    num_todo_define = 0
    for latex_source in latex_files:
        file_str = read_file_str(latex_source)
        num_todo_define += file_str.count("\\tododefine")
    num_todo_define -= 1  # Ignore the definition of the \tododefine macro itself.
    if num_todo_define > MAX_TODODEFINE_INSTANCES:
        # Disallow adding new \tododefines
        print(
            f"ERROR: There are {num_todo_define} occurrences of \\tododefine,\
               expected at most {MAX_TODODEFINE_INSTANCES}"
        )
        return num_todo_define
    else:
        print(f"WARNING: There are {num_todo_define} occurrences of \\tododefine")
        return 0


def check_repeated_words(filename: str) -> int:
    r"""
    Checks if 'file' contains occurrences of the same word
    repeated twice, independent of case. For example, "the the".
    Errors are reported for the file name 'filename' and the total
    number of found errors is returned.
    """
    num_errors = 0
    line_number = 0
    last_token = ""
    for line in read_file_lines(filename):
        line_number += 1
        line = line.strip()
        tokens = re.split(" |{|}", line)
        if not tokens:
            continue
        for current_token in tokens:
            current_token_lower = current_token.lower()
            last_token_lower = last_token.lower()
            if (
                current_token_lower.isalpha()
                and last_token_lower == current_token_lower
            ):
                num_errors += 1
                print(
                    f"./{filename} line {line_number}: \
                        word repetition ({last_token} {current_token}) in '{line}'"
                )
            last_token = current_token
    return num_errors


def detect_incorrect_latex_macros_spacing(filename: str) -> int:
    r"""
    Detects erroneous occurrences of LaTeX macros rendered without
    separation from the next word in 'file'.
    Errors are reported for the file name 'filename' and the total
    number of found errors is returned.
    """
    num_errors = 0
    file_str = read_file_str(filename)
    patterns_to_remove = [
        # Patterns for known math environments:
        r"\$.*?\$",  # $...$
        r"\\\[.*?\\\]",  # \[...\]
        r"\\begin\{mathpar\}.*?\\end\{mathpar\}",  # \begin{mathpar}...\end{mathpar}
        r"\\begin\{equation\}.*?\\end\{equation\}",  # \begin{equation}...\end{equation}
        r"\\begin\{flalign\*\}.*?\\end\{flalign\*\}",  # \begin{flalign*}...\end{flalign*}
        # Macros intended to be preceded by a space character in text mode:
        r"\\item",  # \item occurrences
        r"\\noindent",  # \noindent occurrences
        r"\\tt",  # \tt occurrences
    ]
    for pattern in patterns_to_remove:
        file_str = re.sub(pattern, "", file_str, flags=re.DOTALL)

    # Look for things like \macro word
    macro_followed_by_space = r"\\[a-zA-Z]+(?= )"
    matches = re.findall(macro_followed_by_space, file_str)
    for match in matches:
        print(f'{filename}: LaTeX macro followed by space "{match }"')
        num_errors += 1
    # Look for things like \macro{}word
    macro_followed_by_space = r"\\[a-zA-Z]+{}[a-zA-Z]"
    matches = re.findall(macro_followed_by_space, file_str)
    for match in matches:
        print(f'{filename}: LaTeX macro running into next word "{match}"')
        num_errors += 1
    return num_errors


def check_teletype_in_rule_math_mode(filename) -> int:
    r"""
    Checks that file does not contain \texttt{...} inside math mode
    in rule definitions.
    Otherwise, the errors are reported for 'filename' and the total
    number of errors is returned.
    """
    file_str: str = read_file_str(filename)
    num_errors = 0
    rule_math_mode_patterns = [
        r"\\\[.*?\\\]",  # \[...\]
        r"\\begin\{mathpar\}.*?\\end\{mathpar\}",  # \begin{mathpar}...\end{mathpar}
        r"\\begin\{equation\}.*?\\end\{equation\}",  # \begin{equation}...\end{equation}
    ]
    math_modes_exprs = "|".join(rule_math_mode_patterns)
    math_mode_pattern = re.compile(math_modes_exprs, re.DOTALL)
    teletype_pattern = re.compile(r"\\texttt{.*}")
    matches = math_mode_pattern.findall(file_str)
    for match in matches:
        teletype_vars = teletype_pattern.findall(match)
        for tt_var in teletype_vars:
            print(
                f"{filename}: teletype font not allowed in rules, substitute {tt_var} with a proper macro"
            )
            num_errors += 1
    return num_errors


class RuleBlock:
    r"""
    A class for capturing the lines that a rule consists of,
    the rule type, and the rule name.
    """

    AST_RULE = "AST"
    TYPING_RULE = "Typing"
    SEMANTICS_RULE = "Semantics"

    rule_begin_pattern = re.compile(
        r"\\(TypingRuleDef|SemanticsRuleDef|ASTRuleDef){(.*?)}"
    )
    end_patterns = [
        r"\\section{.*}",
        r"\\subsection{.*}",
        r"\\TypingRuleDef{.*}",
        r"\\SemanticsRuleDef{.*}",
        r"\\ASTRuleDef{.*}",
    ]
    rule_end_pattern = re.compile("|".join(end_patterns))

    def __init__(self, filename, file_lines: list[str], begin: int, end: int):
        self.filename = filename
        self.file_lines = file_lines
        self.begin = begin
        self.end = end

        begin_line = file_lines[begin]
        name_match = re.match(RuleBlock.rule_begin_pattern, begin_line)
        if not name_match:
            self.name = None
            raise ValueError(begin_line)
        else:
            self.name = name_match.group(2)

        if re.search(r"\\ASTRuleDef", begin_line):
            self.type = RuleBlock.AST_RULE
        elif re.search(r"\\TypingRuleDef", begin_line):
            self.type = RuleBlock.TYPING_RULE
        elif re.search(r"\\SemanticsRuleDef", begin_line):
            self.type = RuleBlock.SEMANTICS_RULE
        else:
            self.type = None

    def str(self):
        return f"lines {self.begin+1}-{self.end+1} {self.type}.{self.name}"


def match_rules(filename: str) -> List[RuleBlock]:
    r"""
    Parses 'filename' and returns all AST/Typing/Semantics rules.
    """
    rule_blocks = []
    lines = read_file_lines(filename)
    # The beginning line of a rule block, or -1 meaning outside of a rule.
    current_rule_begin = -1
    for line_number, line in enumerate(lines):
        if RuleBlock.rule_end_pattern.search(line) or line_number == len(lines) - 1:
            if current_rule_begin != -1:
                rule_block = RuleBlock(filename, lines, current_rule_begin, line_number)
                rule_blocks.append(rule_block)
                current_rule_begin = -1
        if RuleBlock.rule_begin_pattern.search(line):
            current_rule_begin = line_number
    return rule_blocks


def check_rule_prose_formally_structure(rule_block: RuleBlock) -> List[str]:
    r"""
    Checks that a rule block contains a single Prose paragraphs followed
    by a single Formally paragraph, returning a list of error messages
    for all errors found.
    """
    num_prose_paragraphs = 0
    num_formally_paragraphs = 0
    block_errors: List[str] = []
    for line_number in range(rule_block.begin, rule_block.end + 1):
        line = rule_block.file_lines[line_number].strip()
        if line.startswith("%"):
            continue
        if re.search(r"\\ProseParagraph", line):
            num_prose_paragraphs += 1
            if num_formally_paragraphs > 0:
                block_errors.append(
                    "encountered a Formally paragraph before Prose paragraph"
                )
        if re.search(r"\\FormallyParagraph", line):
            num_formally_paragraphs += 1
            if num_formally_paragraphs == 0:
                block_errors.append(
                    "encountered a Prose paragraph before Formally paragraph"
                )
    if num_prose_paragraphs == 0:
        block_errors.append("missing a Prose paragraph")
    if num_prose_paragraphs > 1:
        block_errors.append("encountered more than one Prose paragraph")
    if num_formally_paragraphs == 0:
        block_errors.append("missing a Formally paragraph")
    if num_formally_paragraphs > 1:
        block_errors.append("encountered more than one Formally paragraph")
    return block_errors


def check_rule_case_consistency(rule_block: RuleBlock) -> List[str]:
    r"""
    Checks that the rule cases appearing in the Prose paragraph and Formally
    paragraph are equal and each paragraph does not contain duplicate cases.
    """
    prose_cases: Set[str] = set()
    formally_cases: Set[str] = set()
    prose_cases_pattern = re.compile(r".*\\AllApplyCase{(.*?)}")
    formally_cases_pattern = re.compile(r".*\\inferrule\[(.*?)\]")
    error_messages: List[str] = []
    for line_number in range(rule_block.begin, rule_block.end + 1):
        line = rule_block.file_lines[line_number].strip()
        if line.startswith("%"):
            continue
        formally_matches = re.match(formally_cases_pattern, line)
        if formally_matches:
            case_names = formally_matches.group(1).split(",")
            for case_name in case_names:
                case_name = case_name.strip()
                if case_name in formally_cases:
                    error_messages.append(
                        f'Case "{case_name}" duplicate in Formally paragraph'
                    )
                formally_cases.add(case_name)
        prose_matches = re.match(prose_cases_pattern, line)
        if prose_matches:
            matched_case_names = prose_matches.group(1)
            case_names = matched_case_names.split(",")
            for case_name in case_names:
                case_name = case_name.strip()
                if case_name in prose_cases:
                    error_messages.append(
                        f'Case "{case_name}" duplicate in Prose paragraph'
                    )
                prose_cases.add(case_name)
    cases_only_in_prose = prose_cases.difference(formally_cases)
    cases_only_in_formally = formally_cases.difference(prose_cases)
    if cases_only_in_prose:
        error_messages.append(f"cases only in Prose paragraph: {cases_only_in_prose}")
    if cases_only_in_formally:
        error_messages.append(
            f"cases only in Formally paragraph: {cases_only_in_formally}"
        )

    return error_messages


def check_rule_has_example(rule_block: RuleBlock) -> List[str]:
    r"""
    Every typing rule and semantics rule should provide or reference at least
    one example.
    """
    example_found = False
    for line_number in range(rule_block.begin, rule_block.end + 1):
        line = rule_block.file_lines[line_number].strip()
        if line.startswith("\\ExampleDef") or "\\ExampleRef" in line or "\\subsubsection{Example}" in line:
            example_found = True
            break
    error_messages = []
    if not example_found:
        error_messages.append("missing an example")
    return error_messages

def check_rules(filename: str) -> int:
    r"""
    Checks the AST/Typing/Semantics rules in 'filename'
    and returns the total number of errors.
    """
    checks = [
        check_rule_prose_formally_structure,
        # check_rule_case_consistency,
        # check_rule_has_example,
    ]
    num_errors = 0
    rule_blocks: List[RuleBlock] = match_rules(filename)
    rule_blocks = [rule_block for rule_block in rule_blocks if rule_block.type != RuleBlock.AST_RULE]
    global num_rules
    num_rules += len(rule_blocks)
    for rule_block in rule_blocks:
        if not rule_block:
            print(f"{filename} {rule_block.str()}: unable to determine rule type")
            num_errors += 1
            continue
        error_messages: List[str] = []
        for check in checks:
            error_messages.extend(check(rule_block))
        if error_messages:
            error_messages = ", ".join(error_messages)
            print(f"{rule_block.filename} {rule_block.str()}: {error_messages}")
            num_errors += 1
    return num_errors


def check_per_file(latex_files: list[str], checks):
    r"""
    Applies the list of functions in 'checks' to each file in 'latex files',
    accumulating the number of errors and returning the total number of errors
    across all files.
    """
    num_errors = 0
    for filename in latex_files:
        for check in checks:
            num_errors += check(filename)
    return num_errors

def main():
    args = cli_parser.parse_args()
    if args.macros:
        apply_all_macros()
    print("Linting files...")
    all_latex_sources = get_latex_sources(False)
    content_latex_sources = get_latex_sources(True)
    num_errors = 0
    num_errors += check_hyperlinks_and_hypertargets(all_latex_sources)
    num_errors += check_undefined_references_and_multiply_defined_labels()
    num_errors += check_tododefines(content_latex_sources)
    num_errors += check_per_file(
        content_latex_sources,
        [
            check_repeated_words,
            detect_incorrect_latex_macros_spacing,
            # check_teletype_in_rule_math_mode,
            check_rules,
        ],
    )

    #print(f"There are #{num_rules} rules")
    if num_errors > 0:
        print(f"There were {num_errors} errors!", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
