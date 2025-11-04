package main

import (
	"container/heap"
	"container/list"
	"fmt"
	"math/rand"
	"strconv"
	"sync"
	"time"

	"fyne.io/fyne/v2"
	"fyne.io/fyne/v2/app"
	"fyne.io/fyne/v2/container"
	"fyne.io/fyne/v2/dialog"
	"fyne.io/fyne/v2/widget"
)

var n = 3
var idsPath []string // for IDS path building

// ---------- Utility functions ----------

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
	neighbors := make([]string, 0, 4)
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

// ---------- A* ----------

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

	goalKey := serialize(goal)
	cameFrom := make(map[string]string)
	gScore := make(map[string]int)
	pq := &PriorityQueue{}
	heap.Init(pq)

	startKey := serialize(start)
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
			// Reconstruct path
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

// ---------- IDS ----------

//var idsPath []string

func ids(start, goal [][]int, _ int) [][][]int { // maxDepth ignored — we auto-limit
	if !isSolvable(start, goal) {
		return nil
	}
	startKey := serialize(start)
	goalKey := serialize(goal)
	if startKey == goalKey {
		return [][][]int{start}
	}

	idsPath = idsPath[:0] // reuse slice
	depth := 0
	for {
		visited := make(map[string]bool, 1<<16) // 64 KB start, grows safely
		if idsDfs(startKey, goalKey, depth, "", visited) {
			// Convert keys → matrices only once
			path := make([][][]int, len(idsPath))
			for i := range idsPath {
				path[i] = deserialize(idsPath[i])
			}
			return path
		}
		depth++
		if depth > 200 { // safety
			return nil
		}
	}
}

func idsDfs(curr, goal string, depth int, parent string, visited map[string]bool) bool {
	if depth < 0 {
		return false
	}
	if curr == goal {
		idsPath = append(idsPath, curr)
		return true
	}
	if visited[curr] {
		return false
	}
	visited[curr] = true
	defer delete(visited, curr)

	for _, neigh := range getNeighborKeys(curr) {
		if neigh == parent {
			continue
		}
		if idsDfs(neigh, goal, depth-1, curr, visited) {
			idsPath = append(idsPath, curr)
			return true
		}
	}
	return false
}

// ---------- BFS ----------

func bfs(start, goal [][]int) [][][]int {
	if !isSolvable(start, goal) {
		return nil
	}
	startKey := serialize(start)
	goalKey := serialize(goal)
	if startKey == goalKey {
		return [][][]int{start}
	}

	// Forward search
	fwdParent := map[string]string{startKey: ""}
	fwdQ := list.New()
	fwdQ.PushBack(startKey)

	// Backward search
	bwdParent := map[string]string{goalKey: ""}
	bwdQ := list.New()
	bwdQ.PushBack(goalKey)

	for fwdQ.Len() > 0 && bwdQ.Len() > 0 {
		// --- Forward step ---
		if fwdQ.Len() > 0 {
			curr := fwdQ.Remove(fwdQ.Front()).(string)
			if _, ok := bwdParent[curr]; ok {
				return buildPath(fwdParent, bwdParent, curr)
			}
			for _, neigh := range getNeighborKeys(curr) {
				if _, seen := fwdParent[neigh]; !seen {
					fwdParent[neigh] = curr
					fwdQ.PushBack(neigh)
				}
			}
		}

		// --- Backward step ---
		if bwdQ.Len() > 0 {
			curr := bwdQ.Remove(bwdQ.Front()).(string)
			if _, ok := fwdParent[curr]; ok {
				return buildPath(fwdParent, bwdParent, curr)
			}
			for _, neigh := range getNeighborKeys(curr) {
				if _, seen := bwdParent[neigh]; !seen {
					bwdParent[neigh] = curr
					bwdQ.PushBack(neigh)
				}
			}
		}

		// Memory cap: stop if too big
		if len(fwdParent)+len(bwdParent) > 2_000_000 { // ~40 MB safe limit
			return nil
		}
	}
	return nil
}

// Helper: reconstruct path from meeting point
func buildPath(fwd, bwd map[string]string, meet string) [][][]int {
	// Forward part
	var path []string
	cur := meet
	for cur != "" {
		path = append([]string{cur}, path...)
		cur = fwd[cur]
	}
	// Backward part
	cur = bwd[meet]
	for cur != "" {
		path = append(path, cur)
		cur = bwd[cur]
	}
	// Convert to [][]int
	result := make([][][]int, len(path))
	for i, k := range path {
		result[i] = deserialize(k)
	}
	return result
}

// ---------- GUI ----------

type PuzzleGUI struct {
	window       fyne.Window
	nEntry       *widget.Entry
	modeSelector *widget.RadioGroup
	startEntries [][]*widget.Entry
	goalEntries  [][]*widget.Entry
	timerLabel   *widget.Label
	startTime    time.Time
	running      bool
	mutex        sync.Mutex
}

func main() {
	rand.Seed(time.Now().UnixNano())

	a := app.New()
	w := a.NewWindow("N-Puzzle Solver (A* / BFS / IDS)")
	gui := &PuzzleGUI{window: w}
	gui.buildUI()
	w.Resize(fyne.NewSize(860, 600))
	w.ShowAndRun()
}

func (gui *PuzzleGUI) buildUI() {
	gui.nEntry = widget.NewEntry()
	gui.nEntry.SetText("3")

	gui.modeSelector = widget.NewRadioGroup([]string{"random", "manual"}, func(string) {})
	gui.modeSelector.SetSelected("random")

	gui.timerLabel = widget.NewLabel("Time: 0.00 s")

	top := container.NewHBox(
		widget.NewLabel("Size (n):"), gui.nEntry,
		gui.modeSelector,
		widget.NewButton("Generate", gui.generateGrids),
		widget.NewButton("Solve A*", func() { go gui.solve("astar") }),
		widget.NewButton("Solve BFS", func() { go gui.solve("bfs") }),
		widget.NewButton("Solve IDS", func() { go gui.solve("ids") }),
		gui.timerLabel,
	)

	gui.window.SetContent(container.NewVBox(top))
	gui.generateGrids()
}

func (gui *PuzzleGUI) generateGrids() {
	n64, err := strconv.ParseInt(gui.nEntry.Text, 10, 64)
	if err != nil || n64 < 2 || n64 > 5 {
		dialog.ShowError(fmt.Errorf("n must be between 2 and 5"), gui.window)
		return
	}
	n = int(n64)

	mode := gui.modeSelector.Selected
	var start, goal [][]int
	if mode == "random" {
		for {
			start = randomState(n)
			goal = randomState(n)
			if isSolvable(start, goal) {
				break
			}
		}
	}

	gui.startEntries = make([][]*widget.Entry, n)
	gui.goalEntries = make([][]*widget.Entry, n)

	startGrid := container.NewVBox()
	goalGrid := container.NewVBox()

	for i := 0; i < n; i++ {
		rowStart := container.NewHBox()
		rowGoal := container.NewHBox()
		gui.startEntries[i] = make([]*widget.Entry, n)
		gui.goalEntries[i] = make([]*widget.Entry, n)

		for j := 0; j < n; j++ {
			startEntry := widget.NewEntry()
			if mode == "random" {
				startEntry.SetText(strconv.Itoa(start[i][j]))
			}
			gui.startEntries[i][j] = startEntry
			rowStart.Add(startEntry)

			goalEntry := widget.NewEntry()
			if mode == "random" {
				goalEntry.SetText(strconv.Itoa(goal[i][j]))
			}
			gui.goalEntries[i][j] = goalEntry
			rowGoal.Add(goalEntry)
		}
		startGrid.Add(rowStart)
		goalGrid.Add(rowGoal)
	}

	gui.window.SetContent(container.NewVBox(
		container.NewHBox(
			widget.NewLabel("Size (n):"), gui.nEntry,
			gui.modeSelector,
			widget.NewButton("Generate", gui.generateGrids),
			widget.NewButton("Solve A*", func() { go gui.solve("astar") }),
			widget.NewButton("Solve BFS", func() { go gui.solve("bfs") }),
			widget.NewButton("Solve IDS", func() { go gui.solve("ids") }),
			gui.timerLabel,
		),
		container.NewHBox(
			container.NewVBox(widget.NewLabel("Start State"), startGrid),
			container.NewVBox(widget.NewLabel("Goal State"), goalGrid),
		),
	))
}

func (gui *PuzzleGUI) readGrid(entries [][]*widget.Entry) [][]int {
	grid := make([][]int, n)
	for i := 0; i < n; i++ {
		grid[i] = make([]int, n)
		for j := 0; j < n; j++ {
			val, err := strconv.Atoi(entries[i][j].Text)
			if err != nil {
				return nil
			}
			grid[i][j] = val
		}
	}
	return grid
}

func (gui *PuzzleGUI) solve(algo string) {
	gui.mutex.Lock()
	if gui.running {
		gui.mutex.Unlock()
		return
	}
	gui.running = true
	gui.mutex.Unlock()

	start := gui.readGrid(gui.startEntries)
	goal := gui.readGrid(gui.goalEntries)
	if start == nil || goal == nil {
		fyne.Do(func() {
			dialog.ShowError(fmt.Errorf("enter only numbers"), gui.window)
		})
		gui.mutex.Lock()
		gui.running = false
		gui.mutex.Unlock()
		return
	}
	if !isSolvable(start, goal) {
		fyne.Do(func() {
			dialog.ShowError(fmt.Errorf("puzzle is not solvable!"), gui.window)
		})
		gui.mutex.Lock()
		gui.running = false
		gui.mutex.Unlock()
		return
	}

	gui.startTime = time.Now()
	go gui.updateTimer()

	var solution [][][]int
	switch algo {
	case "astar":
		solution = aStar(start, goal)
	case "bfs":
		solution = bfs(start, goal)
	case "ids":
		solution = ids(start, goal, n*n*5) // Reduced max depth to avoid stack overflow
	}

	gui.mutex.Lock()
	gui.running = false
	gui.mutex.Unlock()

	if solution == nil {
		fyne.Do(func() {
			dialog.ShowError(fmt.Errorf("No solution found!"), gui.window)
		})
		return
	}

	gui.animateSolution(solution)
}

func (gui *PuzzleGUI) updateTimer() {
	for {
		gui.mutex.Lock()
		if !gui.running {
			gui.mutex.Unlock()
			break
		}
		gui.mutex.Unlock()

		time.Sleep(100 * time.Millisecond)

		elapsed := time.Since(gui.startTime).Seconds()
		fyne.Do(func() {
			gui.timerLabel.SetText(fmt.Sprintf("Time: %.2f s", elapsed))
		})
	}
}

func (gui *PuzzleGUI) animateSolution(path [][][]int) {
	go func() {
		textBuf := make([][]string, n)
		for i := range textBuf {
			textBuf[i] = make([]string, n)
		}

		for step, state := range path {
			time.Sleep(500 * time.Millisecond)

			stepIdx := step
			currentState := state

			fyne.Do(func() {
				for i := 0; i < n; i++ {
					for j := 0; j < n; j++ {
						val := currentState[i][j]
						if val == 0 {
							textBuf[i][j] = ""
						} else {
							textBuf[i][j] = strconv.Itoa(val)
						}
						gui.startEntries[i][j].SetText(textBuf[i][j])
					}
				}
				elapsed := time.Since(gui.startTime).Seconds()
				gui.timerLabel.SetText(fmt.Sprintf("Step: %d/%d | Time: %.2f s", stepIdx+1, len(path), elapsed))
			})
		}

		fyne.Do(func() {
			moves := len(path) - 1
			dialog.ShowInformation("Done", fmt.Sprintf("Puzzle solved in %d moves!", moves), gui.window)
		})
	}()
}
