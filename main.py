from typing import List, Tuple, Optional
from typing_extensions import Self

test_string = """
1
'Hello

(+ 1 2)

(judge 1 Int)

(judge a Int)
(define a 2)

-- (+ a 1)

((lambda (x) (+ x x)) 2)

(defun (b) 5)
(b)
(judge b (-> Int))


(define t Type)
(judge t Type)

(defun (idGen t)
 (lambda (x) x)
)

(define idInt (idGen Int))

-- (judge (idGen Int) (-> Int Int))
(idInt 5)


(judge sum Int)
(define sum (+ 1 1))


(defun (square x) (* x x))
(square 3)
(judge square (-> Int Int))

(+ 1 1)



(defun (fib x) ( if (<= x 1) 1 (+ (fib (- x 1)) (fib (- x 2)))))
(judge fib (-> Int Int))
(fib 9)

(define x (fib 4))
(+ x 1)
(judge (fib 2) Int)



(square 2)
(square a)


(judge r2 (-> Int Int Int)))
(define r2 (lambda (x y)
    (let
        (((x2) (square x)))
         ((+ x2 (square y)))
     )))

"""

_ = """
(judge idT (-> Type Type))
(defun (idT t) (-> t t))

(judge idGen (lambda (t) (-> t t)))
(defun (idGen t)
  (let
     ((judgement (judge idT (-> t t)))
      (idT (lambda (x) x))
     )
     idT
  )
)



(defun (id x:t:Type) x)

id:: t:Type -> Type
id: x:t -> t
id x = x

concat:: t:Type -> n:Int -> m:Int -> Type
concat: List t n -> List t m -> List t (n+m)
concat xs ys = xs ++ ys


id x:t:Type -> t =
    x




concat xs:(List t1) ys:(List t2) -> (List t) = xs ++ ys
with
    let
        n = List.len(xs)
        m = List.len(ys)
    in
    t1 == t2
    List.length (concat xs ys) == n + m




add: Units -> Units -> Units
add a b = Units.rawAdd a b
with
    dimensions a == dimensions b
    dimensions a == dimensions (add a b)





mul: Units -> Units -> Units
mul a b = Units.mul a b
with
    dimensions (mul a b) == (Dimensions.add (dimensions a) (dimensions b))






trueIntFalseStr: bool -> (Int|Str)
trueIntFalseStr cond = ...
with
    if cond
        judge (trueIntFalseBool cond) Int
    else
        judge (trueIntFalseBool cond) Str






(judge Bool Type)
(define Bool
    (oneOf
     (('True)
      ('False))))

(judge Maybe (-> Type Type))
(define Maybe
    (lambda (t)
        (oneOf
            (`Nothing)
            (forall (value t) (`Something t))
         )
     )
 )
"""


list_string = """
List: Type -> Type
List t =
    Empty:(List t)
    | Cons:(t -> List t -> List t) head tail

"""


class Env:
    def __init__(self, parent=None, bindings={}):
        self.bindings = {k: v for k, v in bindings.items()}
        self.judgements = {}
        self.deferedJudgements = {}
        self.parent = parent

    def get(self, name: str):
        if name in self.bindings:
            return self.bindings[name]

        if self.parent is not None:
            return self.parent.get(name)

        raise Exception(f"Name '{name}' not found at the root env")

    def set(self, name: str, value) -> None:
        if name in self.deferedJudgements:
            self.check_judgement(name, value)

        if name in self.bindings:
            raise Exception(f"Can't overwrite {name}")

        self.bindings[name] = value

    def has(self, name: str) -> bool:
        if name in self.bindings:
            return True

        if self.parent is not None:
            return self.parent.has(name)

        return False

    def set_judgement(self, name: str, judgement):
        assert isinstance(
            judgement, Judgement), f"{judgement} is not a Judgement"
        if name in self.judgements:
            # TODO allow multiple judgements?
            raise Exception(f"{name} already has a judgement")

        self.judgements[name] = judgement

    def defer_judgement(self, name: str, judgement):
        assert isinstance(
            judgement, Judgement), f"{judgement} is not a Judgement"
        if self.has(name):
            raise Exception(
                f"Attempt to defer judgement on existing binding {name}")

        if self.get_judgement(name) is not None:
            raise Exception(
                f"(Attempt to defer judgement on a name with an existing judgement: {name}")

        if name in self.deferedJudgements is not None:
            raise Exception(
                f"(Attempt to defer judgement on a name with an existing defered judgement: {name}")

        print(f"Defering judgement of {name}")
        self.deferedJudgements[name] = judgement

    def get_judgement(self, name: str):
        if name in self.judgements:
            return self.judgements[name]

        if self.parent is not None:
            return self.parent.get_judgement(name)

    def get_defJudgement(self, name: str):
        if name in self.deferedJudgements:
            return self.deferedJudgements[name]

        if self.parent is not None:
            return self.parent.get_defJudgement(name)

    def set_axiom(self, name, judgement):
        assert isinstance(
            judgement, Judgement), f"{judgement} is not a Judgement"
        self.judgements[name] = judgement

    def check_judgement(self, name: str, value) -> None:
        childEnv = self.makeChild()
        childEnv.set(name, value)

        print("Checking defered judgement")
        defered_judgement = self.get_defJudgement(name)

        if not defered_judgement.verify(childEnv):
            raise Exception(
                f"Defered judgement for @{name} does not check out")

        self.judgements[name] = defered_judgement

    def makeChild(self):
        child = Env(parent=self)
        return child


def mul(x, y):
    return Value(x.value * y.value)


def add(x, y):
    return Value(x.value + y.value)


def sub(x, y):
    return Value(x.value - y.value)


def lte(x, y):
    return Value(x.value <= y.value)


def lt(x, y):
    return Value(x.value < y.value)


def eq(x, y):
    return Value(x.value == y.value)


def arrow_type(*types):
    return Value(list(types))


PREFIX_INC = " |   "


class Expression:
    def __init__(self):
        self.annotation = None

    def inferType(self, env: Env, prefix: str) -> Optional[Self]:
        return self.annotation

    def evaluate(self, env: Env) -> Tuple[Optional[Self], Env]:
        raise NotImplementedError()

    def checkType(self, annotatedType: Self, env: Env, prefix: str) -> bool:
        if self.annotation is not None and annotatedType == self.annotation:
            return True

        inferedType = self.inferType(env, prefix + PREFIX_INC)
        if inferedType is not None:
            self.annotation = inferedType
            return self.checkType(annotatedType, env, prefix=prefix + PREFIX_INC)

        # self.annotation = annotatedType
        raise NotImplementedError()


class Value(Expression):
    def __init__(self, value, typ=None):
        super().__init__()

        self.value = value

        if isinstance(value, list):
            self.annotation = Value("Type")
            self.value = [Value(v) for v in value]
            return

        if isinstance(value, Value):
            self.value = value.value
            self.annotation = value.annotation
            return

        if typ is not None:
            self.annotation = typ
        elif isinstance(value, bool):
            self.annotation = Value("Bool", Value("Type"))
        elif isinstance(value, int):
            self.annotation = Value("Int", Value("Type"))
        elif isinstance(value, str):
            if value.startswith("'"):
                self.annotation = Value("Str", Value("Type"))
            if value == "Type":
                self.annotation = self
            if value in ["Bool", "Str", "Int"]:
                self.annotation = Value("Type")

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        return (self, env)

    def inferType(self, env: Env, prefix: str) -> Optional[Expression]:
        return self.annotation

    def checkType(self, annotatedType: Expression, env: Env, prefix: str) -> bool:
        print(f"{prefix}{self}.checkType {annotatedType}")
        type_check = self.annotation == annotatedType
        print(f"{prefix} +{self}.checkType {annotatedType} = {type_check}")
        return type_check

    def __eq__(self, other: Self) -> bool:
        if isinstance(other, str):
            return self == Value(other)

        if isinstance(self.value, str) and "Type" == self.value:
            return isinstance(other.value, str) and "Type" == other.value

        if (self.annotation is None) or (other.annotation is None):
            return self.value == other.value

        if (self.annotation == other.annotation):
            return (self.value == other.value)
        else:
            return False

    def __str__(self):
        value_str = str(self.value)

        if self.value == "Type":
            return "Type"

        if isinstance(self.value, list):
            value_str = "(-> " + " ".join(str(s) for s in self.value) + ")"

        if self.annotation is not None:
            return f"{value_str} [{self.annotation}]"
        return str(value_str)


class IfStatement(Expression):
    def __init__(self, condExpr: Expression, trueExpr: Expression, falseExpr: Expression):
        self.condExpr = condExpr
        self.trueExpr = trueExpr
        self.falseExpr = falseExpr

        super().__init__()

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        (cond, _) = self.condExpr.evaluate(env.makeChild())
        if not isinstance(cond.value, bool):
            raise Exception("Conditional expression wasn't a boolean")

        if cond.value:
            return self.trueExpr.evaluate(env.makeChild())
        else:
            return self.falseExpr.evaluate(env.makeChild())

    def inferType(self, env: Env, prefix: str) -> Optional[Expression]:
        return

    def checkType(self, annotatedType: Expression, env: Env, prefix: str) -> bool:
        print(f"{prefix}{self}.checkType {annotatedType}")
        print(
            f"{prefix} + Starting with checking {self.condExpr} against type {Value('Bool')}")

        assert self.condExpr.checkType(
            Value("Bool", "Type"), env, prefix=prefix + PREFIX_INC)

        print(f"{prefix} + checking the true branch...")
        true_match = self.trueExpr.checkType(
            annotatedType, env, prefix=prefix + PREFIX_INC)
        if not true_match:
            print(f"{prefix} + checkType is False on the true branch")
            return False
        else:
            print(f"{prefix} + ok")

        print(f"{prefix} + checking the false branch...")
        false_match = self.falseExpr.checkType(
            annotatedType, env, prefix=prefix + PREFIX_INC)
        if not false_match:
            print(f"{prefix} + checkType is False on the false branch")
            return False
        else:
            print(f"{prefix} + ok")

        print(f"{prefix} + is checks out!")
        return true_match and false_match

    def __str__(self) -> str:
        return f"(if {self.condExpr} {self.trueExpr} {self.falseExpr})"


class Name(Expression):
    def __init__(self, name: str):
        super().__init__()
        self.name = name

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        return env.get(self.name).evaluate(env)

    def inferType(self, env: Env, prefix: str) -> Expression:
        print(f"{prefix}{self}.inferType")
        existingType = self.annotation
        if existingType is not None:
            print(f"{prefix} +.. returning existing judgement {self.annotation}")
            return existingType

        existingJudgement = env.get_judgement(self.name)
        if existingJudgement is not None:
            self.annotation = existingJudgement.judgement
            print(f"{prefix} +.. returning existing judgement {self.annotation}")
            return self.annotation

        val = env.get(self.name)
        if val is None:
            raise Exception("Can't infer type of unbound variable")
        print(f"{prefix} +.. can't figure out type, defering to {val}")
        return val.inferType(env, prefix=prefix + PREFIX_INC)

    def checkType(self, annotatedType: Expression, env: Env, prefix: str) -> bool:
        print(f"{prefix}{self}.checkType {annotatedType}")
        (inferedType, _) = self.inferType(
            env, prefix=prefix + PREFIX_INC).evaluate(env)

        if inferedType is not None:
            print(f"{prefix} +{self}.checkType.. infered {inferedType}")
            type_match = inferedType == annotatedType
            print(f"{prefix} +{self}.checkType.. is {type_match}")
            return type_match

        print(f"{prefix} +Couldn't infer type of {self}, going deeper")
        (val, _) = self.evaluate(env)
        if val is None:
            raise Exception("No value found for {self} during type checking")

        return val.checkType(annotatedType, env, prefix=prefix + PREFIX_INC)

    def __str__(self) -> str:
        return f"@{self.name}"


class Define(Expression):
    def __init__(self, name: str, expr: Expression):
        self.name = name
        self.expr = expr

        super().__init__()

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        env.set(self.name, self.expr)
        return (None, env)

    def __str__(self) -> str:
        return f"(define {self.name} {self.expr})"


class Lambda(Expression):
    def __init__(self, args: List[str], body: Expression):
        super().__init__()

        self.args = args
        self.body = body

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        self.captured_env = env

        def callable(*argExpr: List[Expression]) -> Optional[Expression]:
            bodyEnv = self.captured_env.makeChild()

            for name, arg in zip(self.args, argExpr):
                bodyEnv.set(name, arg)

            return self.body.evaluate(bodyEnv)[0]

        return (Value(callable, None), env)

    def inferType(self, env: Env, prefix: str) -> Optional[Expression]:
        print(f"{prefix}{self}.inferType")
        if len(self.args) == 0:
            inferedType = Value(
                [self.body.inferType(env, prefix=prefix + PREFIX_INC)])
            print(f"{prefix} +{self}.inferType = {inferedType}")
            return inferedType

    def checkType(self, annotatedType: Expression, env: Env, prefix: str) -> bool:
        print(f"{prefix}{self}.checkType {annotatedType}")
        childEnv = env.makeChild()

        (typeValue, _) = annotatedType.evaluate(env)
        types = typeValue.value
        returnType = types.pop()

        for (argName, argType) in zip(self.args, types):
            print(
                f"{prefix} +{self}.checkType..  setting child axiom on {argName} of {argType}")
            childEnv.set_axiom(argName, Judgement(
                expr=Name(argName), typ=argType))

        print(
            f"{prefix} +{self}.checkType..  checking body returns {returnType} given axioms")
        body_check = self.body.checkType(
            returnType, childEnv, prefix=prefix + PREFIX_INC)
        print(f"{prefix} +{self}.checkType..  {body_check}")

        return body_check

    def __str__(self) -> str:
        return f"(lambda ({' '.join(self.args)}) {self.body})"


class Call(Expression):
    def __init__(self, fnExpr: Expression, args: List[Expression]):
        self.fnExpr = fnExpr
        self.args = args

        super().__init__()

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        fn = self.fnExpr
        while not isinstance(fn, Value):
            (fn, _) = fn.evaluate(env.makeChild())
            assert fn is not None, f"In {self}, the function resolved to None"

        assert isinstance(fn, Value), f"Attempt to call non-value {fn}"
        assert callable(
            fn.value), f"Although call is a value, it's not a function: {fn}"

        evaluatedArgs = [a.evaluate(env.makeChild())[0] for a in self.args]
        return (fn.value(*evaluatedArgs), env)

    def inferType(self, env: Env, prefix: str) -> Optional[Expression]:
        print(f"{prefix}{self}.inferType")

        print(f"{prefix} + infering function type..")
        fn_type = self.fnExpr.inferType(env, prefix=prefix + PREFIX_INC)
        if fn_type is None:
            return None
        (fn_type, _) = fn_type.evaluate(env)
        if fn_type is None:
            return None
        print(f"{prefix} + function type = {fn_type}")

        # Infer arg types from function
        print(f"{prefix} + infering argument types..")
        argTypes = [arg.inferType(env, prefix=prefix + PREFIX_INC)
                    for arg in self.args]
        print(f"{prefix} + {' '.join(str(a) for a in argTypes)}")

        return fn_type.value.pop()

    def checkType(self, annotatedType: Expression, env: Env, prefix: str) -> bool:
        print(f"{prefix}{self}.checkType {annotatedType}")

        print(f"{prefix} + looking at function call type..")
        infered_type = self.fnExpr.inferType(env, prefix=prefix + PREFIX_INC)
        assert infered_type is not None
        print(f"{prefix} + function is {infered_type}")
        (call_type, _) = infered_type.evaluate(env)

        print(f"{prefix} + function is {call_type}")
        assert infered_type is not None
        if not isinstance(call_type, Value):
            print(f"{prefix} + call type {call_type} defies analysis")

        # Extract the function type
        call_types = call_type.value

        # Check return type
        return_type = call_types.pop()
        print(f"{prefix} + checking that return type {return_type} is {annotatedType}")
        if return_type != annotatedType:
            print(f"{prefix} + return type {return_type} doesn't match expected type")
            return False
        print(f"{prefix} + ok")

        # Check the arguments
        for arg_expr, arg_type in zip(self.args, call_types):
            print(f"{prefix} + checking arg {arg_expr} with type {arg_type}")
            if not arg_expr.checkType(arg_type, env, prefix=prefix + PREFIX_INC):
                return False
            print(f"{prefix} + ok")

        return True

    def __str__(self):
        return f"({self.fnExpr} {' '.join(str(a) for a in self.args)})"


class Judgement(Expression):
    def __init__(self, expr: Expression, typ: Expression):
        self.expr = expr
        self.judgement = typ

    def evaluate(self, env: Env) -> Tuple[Expression, Env]:

        if isinstance(self.expr, Name):
            name = self.expr.name
            if not env.has(name):
                env.defer_judgement(name, self)
                return (Value("judgement recorded for later verification"), env)

            # Throws an error
            self.verify(env)

            # Only set this after the fact
            env.set_judgement(name, self)
            return (Value(True), env)

        return (Value(self.verify(env)), env)

    def verify(self, env: Env) -> bool:
        print(f"Verifying {self.expr} with judgement {self.judgement}")
        print()

        (evaluatedType, _) = self.judgement.evaluate(env)
        print(f"- Evaluated type for {self.judgement} is {evaluatedType}")
        print()

        print(f"- Checking type of {self.expr} with {evaluatedType}")

        childEnv = env.makeChild()

        if isinstance(self.expr, Name):
            print(f"  Add self-referential axiom on {self.expr}")
            childEnv.set_axiom(self.expr.name, self)

            if env.get(self.expr.name).checkType(evaluatedType, childEnv, prefix="    "):
                return True

            raise Exception(f"Judgement {self} didn't pan out")

        if self.expr.checkType(evaluatedType, env, prefix="  "):
            print(f"Judgement {self} checked out!!")
            return True

        raise Exception(f"Judgement {self} didn't pan out")

    def __str__(self):
        return f"(judge {self.expr} {self.judgement})"


default_env = Env(bindings={
    "+": Value(add),
    "-": Value(sub),
    "*": Value(mul),
    "<=": Value(lte),
    "<": Value(lt),
    "=": Value(eq),
    "Int": Value("Int"),
    "Str": Value("Str"),
    "Bool": Value("Bool"),
    "Type": Value("Type"),
    "->": Value(arrow_type)
})

default_env.set_axiom(
    "+", Judgement(Name("+"), Value(["Int", "Int", "Int"], "Type")))
default_env.set_axiom(
    "*", Judgement(Name("*"), Value(["Int", "Int", "Int"], "Type")))
default_env.set_axiom(
    "-", Judgement(Name("-"), Value(["Int", "Int", "Int"], "Type")))
default_env.set_axiom("<=", Judgement(
    Name("<="), Value(["Int", "Int", "Bool"], "Type")))
default_env.set_axiom("<", Judgement(
    Name("<"), Value(["Int", "Int", "Bool"], "Type")))
default_env.set_axiom("=", Judgement(
    Name("="), Value(["Int", "Int", "Bool"], "Type")))
default_env.set_axiom("Int", Judgement(Name("Int"), Value("Type")))
default_env.set_axiom("Str", Judgement(Name("Str"), Value("Type")))
default_env.set_axiom("Bool", Judgement(Name("Bool"), Value("Type")))


def tokensToExpression(tokens) -> Expression:
    if not isinstance(tokens, list):
        return singleton(tokens)

    if len(tokens) == 0:
        raise Exception("Empty Expression???")

    first_token = tokens.pop(0)
    if first_token == "judge":
        [expr_tokens, judgement_tokens] = tokens
        expr_expr = tokensToExpression(expr_tokens)
        judgement_expr = tokensToExpression(judgement_tokens)
        return Judgement(expr=expr_expr, typ=judgement_expr)

    if first_token == "define":
        [name_token, expr_tokens] = tokens
        expr_tokens = tokensToExpression(expr_tokens)

        return Define(name=name_token, expr=expr_tokens)

    if first_token == "lambda":
        [arg_tokens, body_tokens] = tokens

        body_expr = tokensToExpression(body_tokens)

        return Lambda(args=arg_tokens, body=body_expr)

    if first_token == "if":
        [cond_tokens, true_tokens, false_tokens] = tokens
        cond_expr = tokensToExpression(cond_tokens)
        true_expr = tokensToExpression(true_tokens)
        false_expr = tokensToExpression(false_tokens)

        return IfStatement(condExpr=cond_expr, trueExpr=true_expr, falseExpr=false_expr)

    if first_token == "defun":
        [[name, *argnames], body] = tokens
        body_expr = tokensToExpression(body)
        return Define(name=name, expr=Lambda(args=argnames, body=body_expr))

    return Call(tokensToExpression(first_token), [tokensToExpression(t) for t in tokens])


def singleton(token: str) -> Expression:
    try:
        num = int(token)
        return Value(num)
    except:
        pass

    if isinstance(token, str):
        if token.startswith("'"):
            return Value(token)
        else:
            return Name(token)

    if isinstance(token, Expression):
        return token

    return Value(token)


def makeNextExpression(tokens: List[str]):
    current_expr = []
    while len(tokens) > 0:
        t = tokens.pop(0)

        if t == "(":
            t, tokens = makeNextExpression(tokens)
        elif t == ")":
            return (current_expr, tokens)

        current_expr.append(t)

    return (current_expr, tokens)


def parse(code_string: str) -> List[Expression]:
    special_chars = ["(", ")"]

    lines = [l.split("--", 1)[0] for l in code_string.splitlines()]

    code_string = "\n".join(lines)

    for s in special_chars:
        code_string = code_string.replace(s, f" {s} ")
    tokens = [t for t in code_string.split() if len(t) > 0]

    exprs_str, _ = makeNextExpression(tokens)

    expressions = []
    for single_expr_tokens in exprs_str:
        expr = tokensToExpression(single_expr_tokens)
        expressions.append(expr)
    return expressions

def evalString(code_string: str) -> str:
    env: Env = default_env
    exprs = parse(code_string)
    results = []
    for expr in exprs:
        (res, env) = expr.evaluate(env)
        if res is not None:
            results.append(str(res))
    return "\n".join(results)

def main() -> None:
    parsed: List[Expression] = parse(test_string)
    env: Env = default_env

    for expr in parsed:
        print(f"> {expr}")
        (res, env) = expr.evaluate(env)
        if res is not None:
            print(res)
        print()

    while True:
        entry = input("> ")
        if entry == "exit":
            break

        exprs = parse(entry)
        for expr in exprs:
            (res, env) = expr.evaluate(env)
            if res is not None:
                print(res)

if __name__ == "__main__":
    main()
