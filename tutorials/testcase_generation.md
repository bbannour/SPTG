
<script type="text/javascript" src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>
<script type="text/x-mathjax-config"> MathJax.Hub.Config({ tex2jax: {inlineMath: [['$', '$']]}, messageStyle: "none" });</script>

# Test case generation

The construction of the test case is obtained by applying dedicated symbolic execution techniques to the reference timed symbolic automaton, in order to derive a symbolic subtree restricted to the test purpose, i.e., a path represented as a sequence of transitions of the reference automaton. In the following, we **first provide an overview of these test-oriented symbolic techniques**, and **then describe the test case generation itself**, obtained by applying transformations to this subtree (mirroring and constraint simplifications).

## 1. Test-oriented Symbolic Execution Techniques

**Symbolic execution** explores a model by representing both data and time with symbolic variables instead of concrete values. It unfolds the automaton while generating constraints over symbolic variables, producing a **symbolic execution tree** . The tree's nodes are **execution contexts**, and its edges represent symbolic steps such as initialization, transition firing, or **quiescence completion**.


### Execution Contexts

An **execution context** $ec=(q, \pi, \lambda, ev, pec)$ consists of:
* The current state $q$.
* The **path condition** $\pi$ (accumulated constraints).
* The mapping $\lambda$ of variables and clocks to symbolic terms.
* The triggering event $ev$.
* The predecessor context $pec$.



The **root context** $ec_0$ starts in $q_0$, with clocks at zero, variables assigned fresh symbols, $\pi = True$, and $ev$ and $pec$ undefined. Initialization produces the first successor, $ec_1$.

**Symbolic Variables**: Fresh symbolic variables are introduced:

$x_0$, $x_1$, ... represent successive values of a data variable $x$ (with $x_0$ being the initial value).

&#35;1, &#35;2, ... denote **symbolic delays**.

&#36;1, &#36;2, ...  denote **emitted values** typed according to their channels.


### Symbolic Paths

Contexts $ec_2$, $ec_3$, and $ec_4$ illustrate the symbolic execution of transitions $\mathbf{tr}_1$, $\mathbf{tr}_2$, and $\mathbf{tr}_3$.

1.  **Edge from $ec_1$ to $ec_2$ ($\mathbf{tr}_1$)**:
    * Transition from $q_0$ to $q_1$ via input $In$.
    * $x$ is updated to x1. Clock $cl$ is reset to $0$.
    * Edge label: symbolic action $\mathit{In}?x_1$ and delay #1.
    * **Path condition**: $1 \leq$ x1 $\leq 10$ (from guard $1 \leq x \leq 10$).
    * Update: $\mathit{sum} \mapsto$ x1.

2.  **Edge from $ec_2$ to $ec_3$ ($\mathbf{tr}_2$)**:
    * Transition from $q_1$ to $q_0$, emitting on channel $\mathit{Out}$.
    * #2 is elapsed time, and $1 is the emitted value. Clock value becomes #2.
    * **Path condition**: x1 $\leq 5$ and #2 = 42 -  x1 (from guard $x \leq 5$ and $cl = 42 - x$), and $1 = 0.

The symbolic path $ec_1.ec_2.ec_3$ corresponds to model path $\mathbf{tr}_1.\mathbf{tr}_2$, yielding the symbolic trace (#1, $\mathit{In}?$ x1).(#2, $\mathit{Out}!$ $1)$.

The **path condition** for this trace ($\#_1$ is unconstrained) is:
$$1 \leq x_1 \leq 10 \;\land\; x_1 \leq 5 \;\land\; \#_2 = 42 - x_1 \;\land\; \$_1 = 0$$

This is **satisfiable** (e.g., $x_1 \mapsto 1$, $\$_1 \mapsto 0$, $\#_1 \mapsto 0$, $\#_2 \mapsto 41$), producing the **timed trace** $(0, \mathit{In}?1).(41, \mathit{Out}!0)$. This trace shows the system receives $\mathit{In}?1$ after initialization and emits $\mathit{Out}!0$ 41 time units later.

---

### Completion by Quiescence

Contexts $ec_5$ and $ec_6$ model **quiescence** (system silence). Symbolic variables are reused across sibling contexts (e.g., $\#_1$ for $ec_2$ and $ec_5$).

* **Quiescence Context $ec_5$**: Derived from $ec_1$. The edge is labeled with the quiescence event $(\#_1, \delta!)$. The system may remain silent indefinitely, reflected by $\pi = \text{True}$ and unconstrained delay $\#_1$.

* **Quiescence Context $ec_6$**: Derived from $ec_2$'s output successors ($ec_3$ and $ec_4$). Its path condition is a disjunction of existential constraints (e.g., $\mathbf{\exists \# \cdot \exists \$_1 \cdot  \#_2 < \# \wedge \ldots}$), capturing that quiescence persists until an output is possible.

* **Trace-Determinism and Pruning**: For a chosen Test Path (TP) $ec_1.ec_2.ec_3$ (which implies $x_1 \le 5$), context $ec_4$ (which implies $x_1 > 5$) **conflicts** and is removed (grayed out). This simplifies $ec_6$'s path condition.

A **witness timed trace** $(0, \mathit{In}?1)\cdot(40, \delta!)$ covers $ec_6$ (with $x_1 \mapsto 1$, $\#_2 \mapsto 40$), demonstrating that after $\mathit{In}?1$, the system can remain silent for 40 time units, expecting the next output at 41.