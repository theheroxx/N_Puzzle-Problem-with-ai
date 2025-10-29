package main

import (
	"container/heap"
	"container/list"
	"fmt"
	"math/rand"

	//"strconv"
	"time"
)

var n = 3

// ---------------- Utility Functions ----------------

func randomState(size int) [][]int {
	nums := rand.Perm(size * size)
	state := make([][]int, size)
	for i := 0; i < size; i++ {
		state[i] = nums[i*size : (i+1)*size]
	}
	return state
}

func flattenAndInversions(matrix [][]int) ([]int, int) {
	flat := []int{}
	for _, row := range matrix {
		for _, num := range row {
			if num != 0 {
				flat = append(flat, num)
			}
		}
	}
	inv := 0
	for i := 0; i < len(flat); i++ {
		for j := i + 1; j < len(flat); j++ {
			if flat[i] > flat[j] {
				inv++
			}
		}
	}
	return flat, inv
}

func blankRowBottom(matrix [][]int) int {
	for i := len(matrix) - 1; i >= 0; i-- {
		for _, v := range matrix[i] {
			if v == 0 {
				return len(matrix) - i
			}
		}
	}
	return 0
}

func isSolvable(start, goal [][]int) bool {
	_, invStart := flattenAndInversions(start)
	_, invGoal := flattenAndInversions(goal)

	if n%2 == 1 {
		return invStart%2 == invGoal%2
	}
	blankStart := blankRowBottom(start)
	blankGoal := blankRowBottom(goal)
	return (invStart+blankStart)%2 == (invGoal+blankGoal)%2
}

func manhattan(state, goal [][]int) int {
	goalPos := make(map[int][2]int, n*n)
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			goalPos[goal[i][j]] = [2]int{i, j}
		}
	}
	distance := 0
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			value := state[i][j]
			if value == 0 {
				continue
			}
			p := goalPos[value]
			distance += absInt(i-p[0]) + absInt(j-p[1])
		}
	}
	return distance
}

func absInt(a int) int {
	if a < 0 {
		return -a
	}
	return a
}

func copyMatrix(m [][]int) [][]int {
	cp := make([][]int, len(m))
	for i := range m {
		cp[i] = append([]int(nil), m[i]...)
	}
	return cp
}

func getNeighbors(state [][]int) [][][]int {
	neighbors := [][][]int{}
	var x, y int
	for i, row := range state {
		for j, v := range row {
			if v == 0 {
				x, y = i, j
				goto found
			}
		}
	}
found:
	moves := [][2]int{{-1, 0}, {1, 0}, {0, -1}, {0, 1}}
	for _, mv := range moves {
		nx, ny := x+mv[0], y+mv[1]
		if nx >= 0 && ny >= 0 && nx < n && ny < n {
			newState := copyMatrix(state)
			newState[x][y], newState[nx][ny] = newState[nx][ny], newState[x][y]
			neighbors = append(neighbors, newState)
		}
	}
	return neighbors
}

func serialize(state [][]int) string {
	b := make([]byte, n*n)
	k := 0
	for _, row := range state {
		for _, v := range row {
			b[k] = byte(v)
			k++
		}
	}
	return string(b)
}

func deserialize(s string) [][]int {
	b := []byte(s)
	state := make([][]int, n)
	for i := 0; i < n; i++ {
		state[i] = make([]int, n)
		for j := 0; j < n; j++ {
			state[i][j] = int(b[i*n+j])
		}
	}
	return state
}

// ---------------- A* Algorithm ----------------

type Node struct {
	est   int
	cost  int
	state [][]int
}

type PriorityQueue []*Node

func (pq PriorityQueue) Len() int           { return len(pq) }
func (pq PriorityQueue) Less(i, j int) bool { return pq[i].est < pq[j].est }
func (pq PriorityQueue) Swap(i, j int)      { pq[i], pq[j] = pq[j], pq[i] }
func (pq *PriorityQueue) Push(x any)        { *pq = append(*pq, x.(*Node)) }
func (pq *PriorityQueue) Pop() any {
	old := *pq
	nn := len(old)
	x := old[nn-1]
	*pq = old[0 : nn-1]
	return x
}

func aStar(start, goal [][]int) [][][]int {
	if !isSolvable(start, goal) {
		return nil
	}

	startKey := serialize(start)
	goalKey := serialize(goal)
	cameFrom := make(map[string]string)
	gScore := make(map[string]int)
	pq := &PriorityQueue{}
	heap.Init(pq)

	gScore[startKey] = 0
	heap.Push(pq, &Node{est: manhattan(start, goal), cost: 0, state: start})

	closed := make(map[string]bool)

	for pq.Len() > 0 {
		item := heap.Pop(pq).(*Node)
		currKey := serialize(item.state)
		if closed[currKey] {
			continue
		}
		if currKey == goalKey {
			path := [][][]int{}
			cur := currKey
			for cur != "" {
				path = append([][][]int{deserialize(cur)}, path...)
				cur = cameFrom[cur]
			}
			return path
		}
		closed[currKey] = true

		for _, neigh := range getNeighbors(item.state) {
			nkey := serialize(neigh)
			tentG := item.cost + 1
			if closed[nkey] {
				continue
			}
			if _, ok := gScore[nkey]; !ok || tentG < gScore[nkey] {
				cameFrom[nkey] = currKey
				gScore[nkey] = tentG
				heap.Push(pq, &Node{est: tentG + manhattan(neigh, goal), cost: tentG, state: neigh})
			}
		}
	}
	return nil
}

// ---------------- BFS ----------------

func getNeighborKeys(current string) []string {
	b := []byte(current)
	var blank int
	for i := range b {
		if b[i] == 0 {
			blank = i
			break
		}
	}
	row, col := blank/n, blank%n
	moves := [][2]int{{-1, 0}, {1, 0}, {0, -1}, {0, 1}}
	neighbors := []string{}
	for _, mv := range moves {
		nr, nc := row+mv[0], col+mv[1]
		if nr >= 0 && nc >= 0 && nr < n && nc < n {
			newB := make([]byte, len(b))
			copy(newB, b)
			swapIdx := nr*n + nc
			newB[blank], newB[swapIdx] = newB[swapIdx], newB[blank]
			neighbors = append(neighbors, string(newB))
		}
	}
	return neighbors
}

func bfs(start, goal [][]int) [][][]int {
	if !isSolvable(start, goal) {
		return nil
	}
	startKey := serialize(start)
	goalKey := serialize(goal)
	parent := make(map[string]string)
	parent[startKey] = ""
	queue := list.New()
	queue.PushBack(startKey)

	for queue.Len() > 0 {
		elem := queue.Remove(queue.Front()).(string)
		if elem == goalKey {
			pathKeys := []string{}
			cur := elem
			for cur != "" {
				pathKeys = append([]string{cur}, pathKeys...)
				cur = parent[cur]
			}
			path := make([][][]int, len(pathKeys))
			for i, k := range pathKeys {
				path[i] = deserialize(k)
			}
			return path
		}
		for _, mv := range getNeighborKeys(elem) {
			if _, exists := parent[mv]; !exists {
				parent[mv] = elem
				queue.PushBack(mv)
			}
		}
	}
	return nil
}

// ---------------- IDS ----------------

func idsD(state, goal [][]int, d int, visited map[string]bool) [][][]int {
	if serialize(state) == serialize(goal) {
		return [][][]int{state}
	}
	if d == 0 {
		return nil
	}
	key := serialize(state)
	if visited[key] {
		return nil
	}
	visited[key] = true

	for _, nb := range getNeighbors(state) {
		result := idsD(nb, goal, d-1, visited)
		if result != nil {
			return append([][][]int{state}, result...)
		}
	}
	return nil
}

func ids(start, goal [][]int, maxDepth int) [][][]int {
	if !isSolvable(start, goal) {
		return nil
	}
	for d := 0; d <= maxDepth; d++ {
		visited := make(map[string]bool)
		result := idsD(start, goal, d, visited)
		if result != nil {
			return result
		}
	}
	return nil
}

// ---------------- Main ----------------

func main() {
	rand.Seed(time.Now().UnixNano())

	fmt.Print("Enter puzzle size n (e.g., 3): ")
	fmt.Scanln(&n)

	var mode string
	fmt.Print("Choose input mode ('random' or 'manual'): ")
	fmt.Scanln(&mode)

	var start, goal [][]int
	if mode == "random" {
		for {
			start = randomState(n)
			goal = randomState(n)
			if isSolvable(start, goal) {
				break
			}
		}
	} else {
		start = readGrid("Start")
		goal = readGrid("Goal")
		if !isSolvable(start, goal) {
			fmt.Println("Puzzle is not solvable!")
			return
		}
	}

	fmt.Println("Start State:")
	printGrid(start)
	fmt.Println("Goal State:")
	printGrid(goal)

	var algo string
	fmt.Print("Choose algorithm ('astar', 'bfs', 'ids'): ")
	fmt.Scanln(&algo)

	startTime := time.Now()
	var solution [][][]int
	switch algo {
	case "astar":
		solution = aStar(start, goal)
	case "bfs":
		solution = bfs(start, goal)
	case "ids":
		solution = ids(start, goal, n*n*5)
	default:
		fmt.Println("Invalid algorithm")
		return
	}
	elapsed := time.Since(startTime)

	if solution == nil {
		fmt.Println("No solution found!")
		return
	}

	fmt.Printf("Solved in %d moves | Time: %.2f s\n", len(solution)-1, elapsed.Seconds())
	for step, state := range solution {
		fmt.Printf("Step %d:\n", step)
		printGrid(state)
	}
}

func readGrid(name string) [][]int {
	grid := make([][]int, n)
	fmt.Printf("Enter %d numbers for %s state (0 for blank) row by row:\n", n*n, name)
	for i := 0; i < n; i++ {
		grid[i] = make([]int, n)
		for j := 0; j < n; j++ {
			fmt.Scan(&grid[i][j])
		}
	}
	return grid
}

func printGrid(state [][]int) {
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			fmt.Printf("%2d ", state[i][j])
		}
		fmt.Println()
	}
	fmt.Println()
}
