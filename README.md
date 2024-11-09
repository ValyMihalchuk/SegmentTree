# SegmentTree
Verification of the SegmentTree implemented in Lean

## Description
- This repository contains the implementation of the Segment Tree, described for example [here](https://www2.compute.dtu.dk/courses/02110/2022/diverse/partialsum-dynarray-v2.pdf) (page 10).
- A segment tree supports two operations: processing a range query and updating an array value.
- We store a segment tree as an array (a list) of $2 * n - 1$ elements where  $n$ is the size of the original array. 
- Each internal tree node with index $i < n-1$ contains sum of child nodes $2*i+1$ and $2 * i +2$.
- The elements of the original array are in indices ranging from $n-1$ to $2n-2$.







