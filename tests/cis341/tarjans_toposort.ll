%struct.LLNode = type { i64, %struct.LLNode* }

@nodeA = global %struct.LLNode { i64 2, %struct.LLNode* @nodeB }
@nodeB = global %struct.LLNode { i64 7, %struct.LLNode* null }

@nodeC = global %struct.LLNode { i64 5, %struct.LLNode* @nodeD }
@nodeD = global %struct.LLNode { i64 8, %struct.LLNode* @nodeE }
@nodeE = global %struct.LLNode { i64 9, %struct.LLNode* null }

@nodeF = global %struct.LLNode { i64 4, %struct.LLNode* null }

@nodeG = global %struct.LLNode { i64 10, %struct.LLNode* null }

@nodeH = global %struct.LLNode { i64 2, %struct.LLNode* @nodeI }
@nodeI = global %struct.LLNode { i64 8, %struct.LLNode* null }

@nodeJ = global %struct.LLNode { i64 4, %struct.LLNode* null }

@nodeK = global %struct.LLNode { i64 8, %struct.LLNode* null }

@nodeL = global %struct.LLNode { i64 0, %struct.LLNode* @nodeM }
@nodeM = global %struct.LLNode { i64 4, %struct.LLNode* @nodeN }
@nodeN = global %struct.LLNode { i64 7, %struct.LLNode* @nodeO }
@nodeO = global %struct.LLNode { i64 8, %struct.LLNode* null }

@dag = global [12 x %struct.LLNode*] [ %struct.LLNode* @nodeA, %struct.LLNode* @nodeC, %struct.LLNode* @nodeF, %struct.LLNode* @nodeG, %struct.LLNode* null, %struct.LLNode* @nodeH, %struct.LLNode* null, %struct.LLNode* @nodeJ, %struct.LLNode* null, %struct.LLNode* @nodeK, %struct.LLNode* null, %struct.LLNode* @nodeL ]

@nodesVisited = global [12 x i1] [i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0 ]

@topoSortComputed = global [12 x i64] [ i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1 ]

@topoSortAnswer = global [12 x i64] [ i64 11, i64 6, i64 3, i64 10, i64 1, i64 9, i64 5, i64 8, i64 0, i64 7, i64 2, i64 4 ]



define void @DFSVisit([12 x %struct.LLNode*]* %adjList, [12 x i1]* %visited, [12 x i64]* %topoSort, i64 %curr, i64* %sortIndexAddr) {
  %visitedAddr = getelementptr [12 x i1], [12 x i1]* %visited, i32 0, i64 %curr
  store i1 1, i1* %visitedAddr

  %neighborsAddr = getelementptr [12 x %struct.LLNode*], [12 x %struct.LLNode*]* %adjList, i32 0, i64 %curr
  br label %loadNeighbors

loadNeighbors:
  %neighbors = load %struct.LLNode*, %struct.LLNode** %neighborsAddr
  %nullNeighbors = icmp eq %struct.LLNode* %neighbors, null
  br i1 %nullNeighbors, label %done, label %neighborLoop 

neighborLoop:
  %neighborAddr = getelementptr %struct.LLNode, %struct.LLNode* %neighbors, i32 0, i32 0
  %neighbor = load i64, i64* %neighborAddr

  %nextNeighborAddrAddr = getelementptr %struct.LLNode, %struct.LLNode* %neighbors, i32 0, i32 1
  %nextNeighborAddr = load %struct.LLNode*, %struct.LLNode** %nextNeighborAddrAddr
  store %struct.LLNode* %nextNeighborAddr, %struct.LLNode** %neighborsAddr

  %neighborVisitedAddr = getelementptr [12 x i1], [12 x i1]* %visited, i32 0, i64 %neighbor
  %neighborVisited = load i1, i1* %neighborVisitedAddr

  br i1 %neighborVisited, label %loadNeighbors, label %visitNeighbor
visitNeighbor:
  call void @DFSVisit([12 x %struct.LLNode*]* %adjList, [12 x i1]* %visited, [12 x i64]* %topoSort, i64 %neighbor, i64* %sortIndexAddr)
  br label %loadNeighbors
done:
  %sortIndex = load i64, i64* %sortIndexAddr
  %topoSortAddr = getelementptr [12 x i64], [12 x i64]* %topoSort, i32 0, i64 %sortIndex
  store i64 %curr, i64* %topoSortAddr
  %newSortIndex = sub i64 %sortIndex, 1
  store i64 %newSortIndex, i64* %sortIndexAddr
  ret void
}

define void @tarjanTopoSort([12 x %struct.LLNode*]* %adjList, [12 x i1]* %visited, [12 x i64]* %topoSort) {
  %adjIndexSlot = alloca i64
  store i64 0, i64* %adjIndexSlot
  %sortIndexSlot = alloca i64
  store i64 11, i64* %sortIndexSlot

  br label %DFSLoop
DFSLoop:
  %adjIndex = load i64, i64* %adjIndexSlot
  %indexOOB = icmp eq i64 %adjIndex, 12
  br i1 %indexOOB, label %done, label %visitedCheck
visitedCheck:
  %visitedBitAddr = getelementptr [12 x i1], [12 x i1]* %visited, i32 0, i64 %adjIndex
  %visitedBit = load i1, i1* %visitedBitAddr

  %nextAdjIndex = add i64 %adjIndex, 1
  store i64 %nextAdjIndex, i64* %adjIndexSlot

  br i1 %visitedBit, label %DFSLoop, label %visit
visit:
  call void @DFSVisit([12 x %struct.LLNode*]* %adjList, [12 x i1]* %visited, [12 x i64]* %topoSort, i64 %adjIndex, i64* %sortIndexSlot)
  br label %DFSLoop
done:
  ret void
}

define i1 @sortsEqualRec(i64 %i, [12 x i64]* %expected, [12 x i64]* %computed) {
  %indexOOB = icmp eq i64 %i, 12
  br i1 %indexOOB, label %base, label %rec
base:
  ret i1 1
rec:
  %nextIndex = add i64 %i, 1
  %restEqual = call i1 @sortsEqualRec(i64 %nextIndex, [12 x i64]* %expected, [12 x i64]* %computed)

  %ptrE = getelementptr [12 x i64], [12 x i64]* %expected, i32 0, i64 %i
  %ptrC = getelementptr [12 x i64], [12 x i64]* %computed, i32 0, i64 %i
  %valE = load i64, i64* %ptrE
  %valC = load i64, i64* %ptrC
  %currEqual = icmp eq i64 %valE, %valC

  %bothEqual = and i1 %currEqual, %restEqual
  br i1 %bothEqual, label %equal, label %notEqual

equal:
  ret i1 1
notEqual:
  ret i1 0
}

define i1 @sortsEqual([12 x i64]* %expected, [12 x i64]* %computed) {
  %1 = call i1 @sortsEqualRec(i64 0, [12 x i64]* %expected, [12 x i64]* %computed)
  ret i1 %1
}

define i1 @main(i64 %argc, i8** %argv) {
  call void @tarjanTopoSort([12 x %struct.LLNode*]* @dag, [12 x i1]* @nodesVisited, [12 x i64]* @topoSortComputed)
  %1 = call i1 @sortsEqual([12 x i64]* @topoSortAnswer, [12 x i64]* @topoSortComputed)
  ret i1 %1
}
