"""
FINITE AUTOMATA AND PUSHDOWN AUTOMATA FOR INPUT VALIDATION AND PARSING
Course: 21CSC301T - Formal Language and Automata
Student: Onkar Upare (RA2411026050001)

Task 2:
1. Four-digit PIN validator using a DFA.
2. Password validator using a product-DFA style state (length + four flags).
3. Simplified email-format validator using the regular expression in the report.

Task 3:
A. Balanced-parentheses checker using a stack (PDA idea).
B. Arithmetic-expression validator/parser using the unambiguous grammar:
       E -> E + T | T
       T -> T * F | F
       F -> (E) | id
   The implementation uses recursive descent after removing left recursion.
C. Palindrome checker over {a, b}, using a nondeterministic PDA idea:
   it tries each possible middle position and matches the second half
   against the stack.
"""

import re


# ============================================================
# TASK 2: FINITE AUTOMATA FOR REAL-TIME VALIDATION
# ============================================================

# ---------------------- 1. PIN DFA ---------------------------

def validate_pin(pin: str) -> bool:
    """
    DFA states:
      q0: 0 digits read
      q1: 1 digit read
      q2: 2 digits read
      q3: 3 digits read
      q4: exactly 4 digits read (accepting)
      dead: invalid character or more than 4 digits
    """
    state = "q0"

    transitions = {
        "q0": {"digit": "q1", "other": "dead"},
        "q1": {"digit": "q2", "other": "dead"},
        "q2": {"digit": "q3", "other": "dead"},
        "q3": {"digit": "q4", "other": "dead"},
        "q4": {"digit": "dead", "other": "dead"},
        "dead": {"digit": "dead", "other": "dead"},
    }

    for char in pin:
        symbol = "digit" if char in "0123456789" else "other"
        state = transitions[state][symbol]

    return state == "q4"


# -------------------- 2. PASSWORD DFA ------------------------

def validate_password(password: str) -> bool:
    """
    Product-DFA state:
      (n, upper, lower, digit, special)
    n is the length read so far, capped at 8.
    Each flag is 0 or 1.

    Required:
      - At least 8 characters
      - At least one uppercase letter
      - At least one lowercase letter
      - At least one digit
      - At least one special character from @ # $ % ! & *
      - No characters outside these classes
    """
    allowed_special = "@#$%!&*"
    allowed = set(
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        "abcdefghijklmnopqrstuvwxyz"
        "0123456789"
        + allowed_special
    )

    # Start state: (length, uppercase, lowercase, digit, special)
    n, upper, lower, digit, special = 0, 0, 0, 0, 0

    for char in password:
        if char not in allowed:
            return False

        n = min(n + 1, 8)

        if char.isupper():
            upper = 1
        elif char.islower():
            lower = 1
        elif char.isdigit():
            digit = 1
        elif char in allowed_special:
            special = 1

    # Accepting state: (8, 1, 1, 1, 1)
    return n == 8 and upper == 1 and lower == 1 and digit == 1 and special == 1


# ---------------------- 3. EMAIL DFA --------------------------

EMAIL_PATTERN = re.compile(
    r"[A-Za-z0-9]+([._][A-Za-z0-9]+)*"
    r"@[A-Za-z0-9]+(\.[A-Za-z0-9]+)*\.[A-Za-z]{2,}"
)


def validate_email(email: str) -> bool:
    """
    Validates the simplified email format described in the report:
      local part: alphanumeric groups separated by one '.' or '_'
      @
      domain labels separated by '.'
      final TLD: at least two letters

    Hyphens, quoted local parts and IP-literal domains are not supported.
    """
    return EMAIL_PATTERN.fullmatch(email) is not None


# ============================================================
# TASK 3: CASE STUDIES WITH PDA AND CFG
# ============================================================

# ---------------- A. BALANCED PARENTHESES PDA ---------------

def validate_parentheses(expression: str) -> bool:
    """
    PDA idea:
      - Push a marker for every '('.
      - Pop one marker for every ')'.
      - Reject if ')' is read when the stack is empty.
      - Accept if the stack is empty at the end.
    """
    stack = []

    for char in expression:
        if char == "(":
            stack.append("X")
        elif char == ")":
            if not stack:
                return False
            stack.pop()
        else:
            # The language in the report contains only '(' and ')'.
            return False

    return len(stack) == 0


# ---------------- B. ARITHMETIC EXPRESSION PARSER ------------

class ExpressionParser:
    """
    Recursive-descent parser for the grammar after removing left recursion:

        E  -> T E'
        E' -> + T E' | epsilon
        T  -> F T'
        T' -> * F T' | epsilon
        F  -> ( E ) | id

    This grammar gives '*' higher precedence than '+' and uses
    left associativity for both operators.
    """

    def __init__(self, expression: str):
        self.tokens = self._tokenize(expression)
        self.position = 0

    @staticmethod
    def _tokenize(expression: str):
        # The report uses the terminal "id". Whitespace is ignored.
        compact = expression.replace(" ", "").replace("\t", "").replace("\n", "")
        tokens = re.findall(r"id|[+*()]", compact)

        # Ensure that every character belongs to a recognized token.
        if "".join(tokens) != compact:
            raise ValueError("Invalid character or token in expression")

        return tokens

    def _current(self):
        if self.position < len(self.tokens):
            return self.tokens[self.position]
        return None

    def _eat(self, expected):
        if self._current() == expected:
            self.position += 1
        else:
            raise ValueError(f"Expected '{expected}', found '{self._current()}'")

    def parse(self) -> bool:
        if not self.tokens:
            return False

        self._parse_expression()

        # All input tokens must be consumed.
        return self.position == len(self.tokens)

    def _parse_expression(self):
        # E -> T E'
        self._parse_term()

        # E' -> + T E' | epsilon
        while self._current() == "+":
            self._eat("+")
            self._parse_term()

    def _parse_term(self):
        # T -> F T'
        self._parse_factor()

        # T' -> * F T' | epsilon
        while self._current() == "*":
            self._eat("*")
            self._parse_factor()

    def _parse_factor(self):
        # F -> ( E ) | id
        if self._current() == "id":
            self._eat("id")
        elif self._current() == "(":
            self._eat("(")
            self._parse_expression()
            self._eat(")")
        else:
            raise ValueError(f"Expected 'id' or '(', found '{self._current()}'")


def validate_expression(expression: str) -> bool:
    """Returns True if the expression follows the CFG, otherwise False."""
    try:
        parser = ExpressionParser(expression)
        return parser.parse()
    except (ValueError, RecursionError):
        return False


# ---------------- C. PALINDROME PDA OVER {a, b} --------------

def validate_palindrome(word: str) -> bool:
    """
    Nondeterministic PDA idea for L = { w : w = reverse(w) } over {a, b}.

    The PDA guesses the middle:
      - Even length: switch to matching mode without consuming a symbol.
      - Odd length: consume and skip the middle symbol while switching.
      - Push the first half onto the stack.
      - Match the remaining input with the stack in reverse order.

    The function tries every possible middle position, representing
    the PDA's nondeterministic choices.
    """
    if any(char not in "ab" for char in word):
        return False

    length = len(word)

    # Try every possible split point for an even-length palindrome.
    for middle in range(length + 1):
        first_half = word[:middle]
        second_half = word[middle:]

        if len(first_half) == len(second_half):
            stack = list(first_half)
            remaining = True

            for char in second_half:
                if not stack or stack.pop() != char:
                    remaining = False
                    break

            if remaining and not stack:
                return True

    # Try every possible skipped middle symbol for odd-length strings.
    for middle in range(length):
        first_half = word[:middle]
        skipped_middle = word[middle]
        second_half = word[middle + 1:]

        if skipped_middle not in "ab" or len(first_half) != len(second_half):
            continue

        stack = list(first_half)
        remaining = True

        for char in second_half:
            if not stack or stack.pop() != char:
                remaining = False
                break

        if remaining and not stack:
            return True

    return False


# ============================================================
# SAMPLE TESTS / OUTPUT
# ============================================================

def run_task2_tests():
    print("\n========== TASK 2: FINITE AUTOMATA ==========")

    print("\nPIN Validator:")
    for value in ["1234", "0000", "123", "12345", "12a4", ""]:
        print(f"{value!r:10} -> {'Accepted' if validate_pin(value) else 'Rejected'}")

    print("\nPassword Validator:")
    for value in [
        "Srm@2026",
        "Pa$$w0rdAI",
        "Zx9!Zx9!",
        "Fla#Auto1",
        "srm@2026",
        "Sr@2026",
    ]:
        print(f"{value:15} -> {'Accepted' if validate_password(value) else 'Rejected'}")

    print("\nEmail Validator:")
    for value in [
        "john.doe@srmist.edu.in",
        "student_01@gmail.com",
        "a@b.in",
        "AI2026@srm.ac.in",
        "john@@gmail.com",
        "john@gmail.c0m",
    ]:
        print(f"{value:30} -> {'Accepted' if validate_email(value) else 'Rejected'}")


def run_task3_tests():
    print("\n========== TASK 3: PDA AND CFG ==========")

    print("\nA. Balanced Parentheses:")
    for value in ["(())", "()()()", "(()", "())", ")(", ""]:
        print(f"{value!r:10} -> {'Accepted' if validate_parentheses(value) else 'Rejected'}")

    print("\nB. Arithmetic Expression:")
    for value in ["id+id*id", "(id+id)*id", "id+*id", "(id+id", "id id", "id+"]:
        print(f"{value:15} -> {'Accepted' if validate_expression(value) else 'Rejected'}")

    print("\nC. Palindrome over {a, b}:")
    for value in ["abba", "babab", "aa", "aba", "abab", "abb"]:
        print(f"{value:10} -> {'Accepted' if validate_palindrome(value) else 'Rejected'}")


if __name__ == "__main__":
    run_task2_tests()
    run_task3_tests()
