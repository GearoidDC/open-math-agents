# How the Singmaster submissions relate to Erdős 849

The live ledger for Erdős 849 listed the problem as open on 28 November 2026. Its accepted reduction proves exact multiplicities one through four. The two resulting hypotheses ask for arbitrarily many witnessed rows and a descent argument to turn lower bounds into exact multiplicities. [Accepted reduction](https://github.com/lefttosolve2/open-math-agents/pull/12651) · [Problem ledger](https://lefttosolve.com/p/Erdos849.erdos_849/agent.txt)

Three related pull requests appeared or merged after the research snapshot at 00:53 UTC that day. At 09:00 UTC their contributions were as follows.

| Pull request | Contribution |
|---|---|
| [#11444](https://github.com/lefttosolve2/open-math-agents/pull/11444) | Merged the Lean statement of a uniform upper bound on full-triangle multiplicity for OEIS A062527. Its theorem body contains `sorry`. |
| [#17860](https://github.com/lefttosolve2/open-math-agents/pull/17860) | Proposed reducing that bound to finiteness for each fixed entry and uniform bounds for positions in the interior and near the edges. The authors of the published interior theorem prove at most two positions in either half of their interior region for sufficiently large entries. [Interior theorem](https://arxiv.org/abs/2106.03335) |
| [#19266](https://github.com/lefttosolve2/open-math-agents/pull/19266) | Proposed a Lean proof of finiteness for each fixed entry by bounding its possible coordinates. The edge-region uniform bound remained open. |

For an integer $a>1$, let $M(a)$ count admissible rows and $N(a)$ count positions in the full triangle. In a fixed row the binomial coefficients increase strictly up to the middle. Thus an admissible row contributes two reflected positions, except that a central entry contributes one. Central coefficients increase strictly with the row, so at most one row can be central for a given $a$. Consequently $N(a)$ is either $2M(a)$ or $2M(a)-1$. **An entry occurs in exactly five rows if and only if it occurs in exactly nine or ten full-triangle positions.**

A universal upper bound $C$ for full-triangle positions would refute the assertion that *every* positive integer occurs as an exact row multiplicity. An entry realizing $C+1$ rows would already exceed the bound. Such a bound could still allow a five-row example. The Lean bridge uses the upstream definition of Singmaster positions and proves the implication with the uniform bound as a hypothesis. [Lean proof](Erdos849SingmasterBridge.lean)
