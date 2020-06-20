SlidingPuzzles.tla
------------------

Solution to a variation of [sliding block puzzle](https://en.wikipedia.org/wiki/Sliding_puzzle)
most commonly known as [Klotski](https://en.wikipedia.org/wiki/Klotski).
This specification with some more description can be also found [here](https://github.com/mryndzionek/tlaplus_specs#slidingpuzzlestla)

TLC finds 25955 distinct states. Green node is the starting position.

The Pennant variation has significantly smaller state space of 'only' 1398 states.
Raymond Hettinger talked about this puzzle and the state graph [here](https://youtu.be/_GP9OpZPUYc?t=742).

```tla
W == 4 H == 5

Pennant == {{<<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>},
            {<<2, 0>>, <<3, 0>>}, {<<2, 1>>, <<3, 1>>},
            {<<0, 2>>}, {<<1, 2>>},
            {<<0, 3>>, <<0, 4>>}, {<<1, 3>>, <<1, 4>>},
            {<<2, 3>>, <<3, 3>>}, {<<2, 4>>, <<3, 4>>}}
            
PennantGoal == {<<0, 3>>, <<0, 4>>, <<1, 3>>, <<1, 4>>} \in board
```

Ma's Puzzle has 110804 distinct states.

```tla
W == 5 H == 5

Mas == {{<<0, 0>>, <<1, 0>>, <<2, 0>>},
        {<<3, 0>>, <<4, 0>>,<<4, 1>>},
        {<<0, 1>>, <<1, 1>>}, {<<2, 1>>, <<3, 1>>},
        {<<0, 2>>, <<0, 3>>, <<1, 3>>},
        {<<1, 2>>, <<2, 2>>}, {<<3, 2>>, <<4, 2>>},
        {<<2, 3>>, <<3, 3>>, <<4, 3>>},
        {<<2, 4>>}}
        
MasGoal == {{<<3, 0>>, <<4, 0>>,<<4, 1>>}, {<<3, 1>>, <<3, 2>>, <<4, 2>>}} \subseteq board
```
