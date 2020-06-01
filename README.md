# 冲冲冲？

`make interface`可以将`parser.mly lexer.mll *.mli`编译为`*.cmi *.cmti`，方便merlin的分析

## Syntax

```ocaml
type annot =
  | AnPure
  | AnImpure
  | AnId of string

type ty =
  | TyBool
  | TyNat
  (* TyFun(T1, T2, T3, T4, a) = T1 -> T2 @cps[T3, T4, a] *)
  | TyFun of ty * ty * ty * ty * annot
  | TyId of string

type term = info * annot * term'

and term' =
  | TmVar of string
  | TmFix of annot * string * string * ty option * term
  | TmAbs of annot * string * ty option * term
  | TmApp of annot * term * term
  | TmLet of string * term * term
  | TmShift of annot * string * term
  | TmReset of term
  | TmIf of term * term * term
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmNat of int
  | TmBool of bool
```

# CPS is all you need

[toc]


语言的设计目标，设计思想，形式定义，性质证明，代码使用方法

## Synopsis

```
let (+) = fix add. a b. 
  if iszero a 
  then b
  else add (pred a) (succ b)
in let (*) = fix mul. a b.
  if iszero a 
  then 0 
  else b + (mul (pred a) b)
in let append = fix append. l1 l2.
  lmatch l1 {
    case nil => l2 
    case hd :: tl => hd :: append tl l2
  }
in let choose = lambda l. shift k in (fix choose. l k.
  lmatch l {
    case nil => []
    case hd :: tl => append (k hd) (choose tl k)
  } ) l k
in reset 
    let a = choose [1, 2] in 
    let b = choose [3, 4] in 
    [[a + b * a, a * b + a]];
```

## Build and Run

Suppose the input file is `test.f`. Run the following command to build and run the interpreter.

```bash
./run.sh test.f
```

## Motivation

Constraint-based Typing Rules with Answer Type and Purity Annotation

## Formalization 

### Syntax

$$
\begin{aligned}
a:= & & purity\ annotations:\\
& \alpha & annotation\ variable\\
& p & pure\ annotation\\
& i & impure\ annotation\\
\ \\
A:= & & term\ with\ annotation:\\
& t^a\\
\ \\
t:= & & terms:\\
& x & variable\\
& 0 & \text{cons}tant\ zero \\
& \text{true} & \text{cons}tant\ \text{true}\\
& \text{false} & \text{cons}tant\ \text{false}\\
& \text{nil} & \text{cons}tant\ nil\\
& \text{succ}\ A & \text{succ}essor\\
& \text{pred}\ A & \text{pred}ecessor\\
& \text{iszero}\ A & zero\ test\\
& \text{if}\ A\ \text{then}\ A\ \text{else}\ A & conditional \\
& \lambda^a x.A & abstraction\\
& \text{fix}^a\ f.x.A & \text{fix}point\\
& A@^a A & application\\
& \text{cons}\ A\ A & list\ \text{cons}truction\\
& \text{lmatch}\ A\ \{\text{case}\ \text{nil}\Rightarrow A\ \text{case}\ x::x\Rightarrow A\} & list\ elimination\\
& \text{let}\ x=A\ \text{in}\ A & \text{let}\ binding\\
& \text{reset}\ A & context\ delimination\\
& \text{shift}^a\ x\ \text{in}\ A & context\ capturing\\
\ \\
T:= & & types:\\
& X & type\ variable\\
& \text{Nat} & natural\ type\\
& \text{Bool} & boolean\ type\\
& T\rightarrow T@[T,T,a] & function\ type\\
& \text{List}[T] & list\ type
\end{aligned}
$$

### Evalution Rules

Abstract machine state: $t\ |\ [C,K]$

+ $t$: Term
+ $C$: Inner <u>C</u>ontext
+ $K$: Outer C(<u>K</u>)ontext

#### Shift

$$
\text{shift}\ x\ \text{in}\ t\ |\ [C, K]\rightarrow [x\mapsto\lambda v.\text{reset}\ (C\ v)]t\ |\ [\emptyset,K]
$$

#### Reset

$$
\text{reset}\ t \ |\ [C,K]\rightarrow t\ |\ [\emptyset,C\leadsto K]
$$

#### Application

$$
\begin{aligned}
& t_1\ t_2\ |\ [C,K]\rightarrow t_1\ |\ [(v_1\mapsto v_1\ t_2)\leadsto C,K]\\
& v_1\ t_2\ |\ [C,K]\rightarrow t_2\ |\ [(v_2\mapsto v_1\ v_2)\leadsto C, K]\\
& (\lambda x.t_1)\ v_2\ |\ [C,K]\rightarrow [x\mapsto v_2]t_1\ |\ [C,K]\\
\end{aligned}
$$

#### Value

$$
\begin{aligned}
& v\ |\ [F\leadsto C,K]\rightarrow F(v)\ |\ [C,K]\\
& v\ |\ [\emptyset, C\leadsto K]\rightarrow v\ |\ [C,K]\\
\end{aligned}
$$

PS: $\emptyset(x)=x,\ (A\leadsto B)(x)=B(A(x))$



Suppose $t\ |\ [C,K]$ will be finally evaluated to $v\ |\ [\emptyset, \emptyset]$. 

If $t\ |\ [C, K]\rightarrow t'\ |\ [C',K']\quad C:T_1\rightarrow T_2\quad K: T_3\rightarrow T_4\quad C' :T_1'\rightarrow T_2'\quad K': T_3'\rightarrow T_4'$, 

then there must be $T_4=T_4'$, but $T_1=T_1',T_2=T_2',T_3=T_3'$ are not guaranteed. 

So the typing information of $t$ must contain $T_1$, $T_2$, $T_3$; we call them "**type of $t$**", "**answer type before $t$'s evaluation**", "**answer type after $t$'s evaluation**" respectively. 

PS: $C: T_1\rightarrow T_2$ means $\exist\ t:T_1,\exist v,(t\ |\ [C,\emptyset]\rightarrow^* v\ |\ [\emptyset, \emptyset])\wedge v:T_2$. So do $K:T_3\rightarrow T_4$ 



### Typing Rules (without annotation)

type assumption $\Gamma\vdash t:T@[R,S];TC$:

+ $\Gamma$: Type context
+ $T$: Type of $t$
+ $R$: Answer type before $t$'s evaluation
+ $S$: Answer type after $t$'s evaluation
+ $TC$: <u>T</u>ype-<u>C</u>ontraints

#### Variable

$$
\frac{
	x:T\in \Gamma\quad I=\text{inst}(T)\quad X=\text{fresh}()
}{
	\Gamma\vdash x:I@[X,X];\emptyset
}
$$

PS: $\text{inst}(T)$ means instantiate $T$'s binding variable (for example, $\alpha$ in type scheme $\forall \alpha. \alpha\rightarrow \alpha$)

#### Abstraction

$$
\begin{aligned}
\frac{
	X,Y=\text{fresh}()\quad\Gamma,x:X\vdash t_1:T_1@[R_1,S_1];TC
}{
	\Gamma\vdash (\lambda x.t_1):(X\rightarrow T_1@[R_1,S_1])@[Y,Y];TC
}
\end{aligned}
$$

#### Application

$$
\frac{
	\Gamma\vdash t_1:T_1@[R_1,S_1];TC_1\quad \Gamma\vdash t_2:T_2@[R_2,S_2];TC_2\\
	X,Y=\text{fresh}()\\
	TC=TC_1\cup TC_2\cup\{T_1=T_2\rightarrow X@[Y,R_2],\ R_1=S_2\}
}{
	\Gamma\vdash (t_1\ t_2):X@[Y,S_1];TC
}
$$

#### Shift

$$
\begin{aligned}
\frac{
    X,Y=\text{fresh}()\\
    \Gamma,k:\forall \tau.(X\rightarrow Y@[\tau,\tau])\vdash t_1:T_1@[R_1,S_1];TC\\
    TC'=TC\cup\{T_1=R_1\}
}{
    \Gamma\vdash (\text{shift}\ k\ \text{in}\ t_1):X@[Y,S_1];TC'
}
\end{aligned}
$$

#### Reset

$$
\begin{aligned}
\frac{
	X=\text{fresh}()\quad \Gamma\vdash t_1:T_1@[R_1,S_1];TC\\
	TC'=TC\cup\{T_1=R_1\}
}{
    \Gamma\vdash (\text{reset}\ t_1):S_1@[X,X];TC'
}
\end{aligned}
$$

### Typing Rules (with annotation)

type assumption $\Gamma\vdash t:T@[R,S,a];[TC,AC]$：

+ $\Gamma$: type context
+ $t$: term
+ $T$: type of $t$
+ $R$: answer-type before evaluating $t$
+ $S$: answer-type after evaluating $t$
+ $a$: purity-annotation of $t$
+ $TC$: <u>T</u>ype-<u>C</u>onstraints that $t$ introduces
+ $AC$: <u>A</u>nnotation-<u>C</u>onstraints that $t$ introduces

#### Variable

$$
\frac{
	x:T\in \Gamma，I=\text{inst}(T)，X=\text{fresh}()
}{
	\Gamma\vdash x^p:I@[X,X,p]; [\emptyset,\emptyset]
}
$$

#### Constant

$$
\frac{
    X=\text{fresh}()
}{
    \Gamma\vdash c^p:B@[X,X,p];[\emptyset, \emptyset]
}
$$

#### Abstraction

$$
\begin{aligned}
\frac{
	X,Y,a_2=\text{fresh}()，\Gamma,x:X\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC,AC]\\
	AC'=AC\cup\{a_1\le a_2,\ R_1\ne S_1\Rightarrow a_1=i\}
}{
	\Gamma\vdash (\lambda^{a_2} x.t_1^{a_1})^p:(X\rightarrow T_1@[R_1,S_1,a_2])@[Y,Y,p];[TC,AC']
}
\end{aligned}
$$

#### Application

$$
\frac{
	\Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC_1,AC_1]，\Gamma\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]\\
	X,Y,a_3,a=\text{fresh}()\\
	TC=TC_1\cup TC_2\cup\{T_1=T_2\rightarrow X@[Y,R_2,a_3],\ R_1=S_2\}\\
	AC=AC_1\cup AC_2\cup\{a_1\le a,\ a_2\le a,\ a_3\le a,\ R_1\ne S_1\Rightarrow a_1=i,\ R_2\ne S_2\Rightarrow a_2=i,\ Y\ne R_2\Rightarrow a_3=i\}
}{
	\Gamma\vdash (t_1^{a_1}@^{a_3}t_2^{a_2})^a:X@[Y,S_1,a];[TC,AC]
}
$$

#### Fixpoint

$$
\begin{aligned}
\frac{
    X,Y,Z,R_1',S_1',a_1',a_2=\text{fresh}()\\
    \Gamma,f:(X\rightarrow Y@[R_1',S_1',a_1']),x:X\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC,AC]\\
    TC'=TC\cup\{Y=T_1,\ R_1'=R_1,\ S_1'=S_1\}\\
    AC'=AC\cup\{a_1\le a_2,\ R_1\ne S_1\Rightarrow a_1=i,\ a_1'\le a_1,\ a_1\le a_1'\}
}{
    \Gamma\vdash (\text{fix}^{a_2}\ f.x.t_1^{a_1})^p:(X\rightarrow Y@[R_1,S_1,a_2])@[Z,Z,p];[TC',AC']
}
\end{aligned}
$$

#### Let-polymorphism

$$
\begin{aligned}
\frac{
    \Gamma \vdash v_1^p:T_1@[R_1,R_1,p];[TC_1,AC_1]，T_1'= apply(un\text{if}y(TC_1),T_1) \\
    \Gamma,x:\text{gen}(\Gamma, T_1')\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]\\
    a=\text{fresh}()\\
    TC=TC_1\cup TC_2\\
    AC=AC_1\cup AC_2\cup\{a_2\le a,\ R_2\ne S_2\Rightarrow a_2=i\}
}{
    \Gamma\vdash (\text{let}\ x = v_1^p\ in\ t_2^{a_2})^a:T_2@[R_2,S_2,a];[TC,AC]
}
\end{aligned}
$$

#### Let

$$
\begin{aligned}
\frac{
    \Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC_1,AC_1]，\Gamma,x:T_1\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]\\
    a=\text{fresh}()\\
    TC=TC_1\cup TC_2\cup\{R_1=S_2\}\\
    AC=AC_1\cup AC_2\cup\{a_1\le a,\ a_2\le a,\ R_1\ne S_1\Rightarrow a_1=i,\ R_2\ne S_2\Rightarrow a_2=i\}
}{
    \Gamma\vdash (\text{let}\ x=t_1^{a_1}\ in\ t_2^{a_2})^a:T_2@[R_2,S_1,a];[TC,AC]
}
\end{aligned}
$$

#### If

$$
\frac{
    \Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC_1,AC_1]，\Gamma\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]，\Gamma\vdash t_3^{a_3}:T_3@[R_3,S_3,a_3];[TC_1,AC_1]\\
    a=\text{fresh}()\\
    TC=TC_1\cup TC_2\cup TC_3\cup \{R_1=S_2,\ R_1=S_3,\ R_2=R_3,\ T_2=T_3,\ T_1=Bool\}\\
    AC=AC_1\cup AC_2\cup AC_3\cup \{{a_i\le a\ }^{i=1,2,3},\ {R_j\ne S_j\Rightarrow a_j=i\ }^{j=1,2,3}\}
}{
    \Gamma\vdash (\text{if}\ t_1^{a_1}\ \text{then}\ t_2^{a_2}\ \text{else}\ t_3^{a_3})^a:T_2@[R_2,S_1,a];[TC,AC]
}
$$

#### Shift

$$
\begin{aligned}
\frac{
    X,Y,a_2=\text{fresh}()\\
    \Gamma,k:\forall \tau.(X\rightarrow Y@[\tau,\tau,a_2])\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC,AC]\\
    TC'=TC\cup\{T_1=R_1\}\\
    AC'=AC\cup\{R_1\ne S_1\Rightarrow a_1=i\}
}{
    \Gamma\vdash (\text{shift}^{a_2}\ k\ in\ t_1^{a_1})^i:X@[Y,S_1,i];[TC',AC']
}
\end{aligned}
$$

#### Reset

$$
\begin{aligned}
\frac{
	X=\text{fresh}()，\Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC,AC]\\
	TC'=TC\cup\{T_1=R_1\}\\
    AC'=AC\cup\{R_1\ne S_1\Rightarrow a_1=i\}
}{
    \Gamma\vdash (\text{reset}\ t_1^{a_1})^p:S_1@[X,X,p];[TC',AC']
}
\end{aligned}
$$

#### Succ/Pred

$$
\begin{aligned}
\frac{
    \Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC,AC]\\
    a=\text{fresh}()\\
    TC'=TC\cup\{T_1=\text{Nat}\}\\
    AC'=AC\cup\{a_1\le a,\ R_1\ne S_1\Rightarrow a_1=i\}
}{
	\Gamma\vdash (\text{succ}\ t_1^{a_1})^a:\text{Nat}@[R_1,S_1,a];[TC',AC']
}
\end{aligned}
$$

#### Cons

$$
\begin{aligned}
\frac{
	\Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC_1,AC_1]\quad \Gamma\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]\\
	a=\text{fresh}()\\
	TC=TC_1\cup TC_2\cup\{T_2=\text{List}[T_1],\ S_2=R_1\}\\
	AC=AC_1\cup AC_2\cup\{{a_i\le a\ }^{i=1,2},\ {R_j\ne S_j\Rightarrow a_j=i\ }^{j=1,2}\}
}{
	\Gamma\vdash (\text{cons}\ t_1^{a_1}\ t_2^{a_2})^a:T_2@[R_2,S_1,a];[TC,AC]
}
\end{aligned}
$$

#### LMatch

$$
\begin{aligned}
\frac{
	\Gamma\vdash t_1^{a_1}:T_1@[R_1,S_1,a_1];[TC_1,AC_1]\quad \Gamma\vdash t_2^{a_2}:T_2@[R_2,S_2,a_2];[TC_2,AC_2]\\
    X,a=\text{fresh}()\\
    \Gamma,\text{hd}:X,\text{tl}:\text{List}[X]\vdash t_3^{a_3}:T_3@[R_3,S_3,a_3];[TC_3,AC_3]\\
    TC=TC_1\cup TC_2\cup TC_3\cup\{T_1=\text{List}[X],\ S_2=R_1,\ S_3=R_1,\ R_2=R_3,\ T_2=T_3\}\\
    AC=AC_1\cup AC_2\cup AC_3\cup\{{a_i\le a\ }^{i=1,2,3},\ {R_j\ne S_j\Rightarrow a_j=i\ }^{j=1,2,3}\}
}{
	\Gamma\vdash (\text{lmatch}\ t_1^{a_1}\{\text{case}\ \text{nil}\Rightarrow t_2^{a_2}\quad \text{case}\ \text{hd}::\text{tl}\Rightarrow t_3^{a_3}\})^a:T_2@[R_2,S_1,a];[TC,AC]
}
\end{aligned}
$$


## Property 



abort e := shift (fun () -> e)
call/cc f := shift (fun k -> k (f (fun x -> abort (k x))))
try e with h := call/cc (fun cc -> let raise x = cc (h x) in e)





