# Benors-Algorithm

Ben-Or is a leaderless based decentralized algorithm. It uses binary input over arbitrary input value to solve the consensus in case of tie-breaking situations (as there is no leader to solve the tie). Also, it utilizes randomization to achieve progress. The Ben-Or algorithm has two phases in each round and is common to all nodes. A round gets locked until there are at least N-F (N = nodes, F = Maximum number of faulty nodes) nodes that propose a value. In the first phase of a round, every node tries to propose a value supported (among 0 and 1) by a majority of the nodes (to propose it for the next phase). In the second phase, a node finalizes its decision if it observed more than F+1 nodes propose the same value. If it fails to find a majority in a round, the algorithm makes some nodes to change their votes and proceed to the next round which helps the system to tilt towards a decision.

So, the system eventually converges to a consensus value as the round progresses. So, in this project we have seen how the algorithm behaves in various scenarios (with cap on
the number of rounds), and varying the number of nodes and faulty nodes when the initial input contains mixture of 0’s and 1’s. I was able to model how the algorithm achieved consensus using binary values and randomness.

I have used TLA+ and PlusCal to code this algorithm.
