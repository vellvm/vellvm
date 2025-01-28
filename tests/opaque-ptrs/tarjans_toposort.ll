%struct.LLNode = type { i64, ptr }

@nodeA = global %struct.LLNode { i64 2, ptr @nodeB }
@nodeB = global %struct.LLNode { i64 7, ptr null }

@nodeC = global %struct.LLNode { i64 5, ptr @nodeD }
@nodeD = global %struct.LLNode { i64 8, ptr @nodeE }
@nodeE = global %struct.LLNode { i64 9, ptr null }

@nodeF = global %struct.LLNode { i64 4, ptr null }

@nodeG = global %struct.LLNode { i64 10, ptr null }

@nodeH = global %struct.LLNode { i64 2, ptr @nodeI }
@nodeI = global %struct.LLNode { i64 8, ptr null }

@nodeJ = global %struct.LLNode { i64 4, ptr null }

@nodeK = global %struct.LLNode { i64 8, ptr null }

@nodeL = global %struct.LLNode { i64 0, ptr @nodeM }
@nodeM = global %struct.LLNode { i64 4, ptr @nodeN }
@nodeN = global %struct.LLNode { i64 7, ptr @nodeO }
@nodeO = global %struct.LLNode { i64 8, ptr null }

@dag = global [12 x ptr] [ ptr @nodeA, ptr @nodeC, ptr @nodeF, ptr @nodeG, ptr null, ptr @nodeH, ptr null, ptr @nodeJ, ptr null, ptr @nodeK, ptr null, ptr @nodeL ]

@nodesVisited = global [12 x i1] [i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0 ]

@topoSortComputed = global [12 x i64] [ i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1 ]

@topoSortAnswer = global [12 x i64] [ i64 11, i64 6, i64 3, i64 10, i64 1, i64 9, i64 5, i64 8, i64 0, i64 7, i64 2, i64 4 ]



define void @DFSVisit(ptr %adjList, ptr %visited, ptr %topoSort, i64 %curr, ptr %sortIndexAddr) {
  %visitedAddr = getelementptr [12 x i1], ptr %visited, i32 0, i64 %curr
  store i1 1, ptr %visitedAddr

  %neighborsAddr = getelementptr [12 x ptr], ptr %adjList, i32 0, i64 %curr
  br label %loadNeighbors

loadNeighbors:
  %neighbors = load ptr, ptr %neighborsAddr
  %nullNeighbors = icmp eq ptr %neighbors, null
  br i1 %nullNeighbors, label %done, label %neighborLoop 

neighborLoop:
  %neighborAddr = getelementptr %struct.LLNode, ptr %neighbors, i32 0, i32 0
  %neighbor = load i64, ptr %neighborAddr

  %nextNeighborAddrAddr = getelementptr %struct.LLNode, ptr %neighbors, i32 0, i32 1
  %nextNeighborAddr = load ptr, ptr %nextNeighborAddrAddr
  store ptr %nextNeighborAddr, ptr %neighborsAddr

  %neighborVisitedAddr = getelementptr [12 x i1], ptr %visited, i32 0, i64 %neighbor
  %neighborVisited = load i1, ptr %neighborVisitedAddr

  br i1 %neighborVisited, label %loadNeighbors, label %visitNeighbor
visitNeighbor:
  call void @DFSVisit(ptr %adjList, ptr %visited, ptr %topoSort, i64 %neighbor, ptr %sortIndexAddr)
  br label %loadNeighbors
done:
  %sortIndex = load i64, ptr %sortIndexAddr
  %topoSortAddr = getelementptr [12 x i64], ptr %topoSort, i32 0, i64 %sortIndex
  store i64 %curr, ptr %topoSortAddr
  %newSortIndex = sub i64 %sortIndex, 1
  store i64 %newSortIndex, ptr %sortIndexAddr
  ret void
}

define void @tarjanTopoSort(ptr %adjList, ptr %visited, ptr %topoSort) {
  %adjIndexSlot = alloca i64
  store i64 0, ptr %adjIndexSlot
  %sortIndexSlot = alloca i64
  store i64 11, ptr %sortIndexSlot

  br label %DFSLoop
DFSLoop:
  %adjIndex = load i64, ptr %adjIndexSlot
  %indexOOB = icmp eq i64 %adjIndex, 12
  br i1 %indexOOB, label %done, label %visitedCheck
visitedCheck:
  %visitedBitAddr = getelementptr [12 x i1], ptr %visited, i32 0, i64 %adjIndex
  %visitedBit = load i1, ptr %visitedBitAddr

  %nextAdjIndex = add i64 %adjIndex, 1
  store i64 %nextAdjIndex, ptr %adjIndexSlot

  br i1 %visitedBit, label %DFSLoop, label %visit
visit:
  call void @DFSVisit(ptr %adjList, ptr %visited, ptr %topoSort, i64 %adjIndex, ptr %sortIndexSlot)
  br label %DFSLoop
done:
  ret void
}

define i1 @sortsEqualRec(i64 %i, ptr %expected, ptr %computed) {
  %indexOOB = icmp eq i64 %i, 12
  br i1 %indexOOB, label %base, label %rec
base:
  ret i1 1
rec:
  %nextIndex = add i64 %i, 1
  %restEqual = call i1 @sortsEqualRec(i64 %nextIndex, ptr %expected, ptr %computed)

  %ptrE = getelementptr [12 x i64], ptr %expected, i32 0, i64 %i
  %ptrC = getelementptr [12 x i64], ptr %computed, i32 0, i64 %i
  %valE = load i64, ptr %ptrE
  %valC = load i64, ptr %ptrC
  %currEqual = icmp eq i64 %valE, %valC

  %bothEqual = and i1 %currEqual, %restEqual
  br i1 %bothEqual, label %equal, label %notEqual

equal:
  ret i1 1
notEqual:
  ret i1 0
}

define i1 @sortsEqual(ptr %expected, ptr %computed) {
  %1 = call i1 @sortsEqualRec(i64 0, ptr %expected, ptr %computed)
  ret i1 %1
}

define i1 @main(i64 %argc, ptr %argv) {
  call void @tarjanTopoSort(ptr @dag, ptr @nodesVisited, ptr @topoSortComputed)
  %1 = call i1 @sortsEqual(ptr @topoSortAnswer, ptr @topoSortComputed)
  ret i1 %1
}

; ASSERT EQ: i1 1 = call i1 @main(i64 0, ptr null)
