package tools

import (
	"context"
	"errors"
	"fmt"
	"time"
)

type itNode struct {
	left *itNode
	right *itNode
	parent *itNode
	color RBcolor
	Interval *Interval
	max uint64
	key uint64
	Value interface{}
}

type RBcolor int
const (
	black RBcolor = iota
	red
)

type Interval struct {
	Low uint64
	High uint64
}

type IntervalTree struct {
	ctx context.Context
	root *itNode
	null *itNode
}

func max(a, b, c uint64) uint64 {
	max := a
	if b > max {
		max = b
	}
	if c > max {
		max = c
	}
	return max
}

func NewIntervalTree(ctx context.Context) *IntervalTree {
	node := &itNode{
		left: nil,
		right: nil,
		parent: nil,
		color: black,
	}
	return &IntervalTree{ctx: ctx, root: node, null: node}
}

func (t *IntervalTree) Empty() bool{
	return t.root == t.null
}

func (t *IntervalTree) insert(ctx context.Context, i *Interval, value interface{}) (err error){
	z := &itNode{
		Interval: i,
		Value: value,
	}
	if checkInvalidNode(z) {
		err = errors.New("Node is invalid")
		helper.Logger.Error(ctx, fmt.Sprintf("Failed to insert node into interval tree, err: %v", err))
		return err
	}
	z.key = z.Interval.Low
	y := t.null
	x := t.root
	for x != t.null {
		y = x
		x.max = max(x.Interval.High, x.max, z.Interval.High)
		if z.key < x.key {
			x = x.left
		} else {
			x = x.right
		}		
	}
	z.parent = y
	if y == t.null {
		t.root = z
	} else if z.key < y.key{
		y.left = z
	} else {
		y.right = z
	}
	z.left = t.null
	z.right = t.null
	z.color = red
	z.max = z.Interval.High
	t.insertFixup(z)
	return nil
}

func (t *IntervalTree) insertFixup(z *itNode) {
	for z.parent.color == red {
		if z.parent == z.parent.parent.left {
			y := z.parent.parent.right
			if y.color == red {
				z.parent.color = black
				y.color = black
				z.parent.parent.color = red
				z = z.parent.parent
			} else {
				if z == z.parent.right {
					z = z.parent
					t.leftRotate(z)
				}
				z.parent.color = black
				z.parent.parent.color = red
				t.rightRotate(z.parent.parent)
			}
		} else {
			y := z.parent.parent.left
			if y.color == red {
				z.parent.color = black
				y.color = black
				z.parent.parent.color = red
				z = z.parent.parent
			} else {
				if z == z.parent.left {
					z = z.parent
					t.rightRotate(z)
				}
				z.parent.color = black
				z.parent.parent.color = red
				t.leftRotate(z.parent.parent)
			}
		}
	}
	t.root.color = black
}

func (t *IntervalTree) leftRotate(x *itNode) {
	y := x.right
	x.right = y.left
	if y.left != t.null {
		y.left.parent = x
	}
	y.parent = x.parent
	if x.parent == t.null {
		t.root = y
	} else if x == x.parent.left {
		x.parent.left = y
	} else {
		x.parent.right = y
	}
	y.left = x
	x.parent = y
	y.max = x.max
	x.max = max(x.Interval.High, x.left.max, x.right.max)
}

func (t *IntervalTree) rightRotate(x *itNode) {
	y := x.left
	x.left = y.right
	if y.right != t.null {
		y.right.parent = x
	}
	y.parent = x.parent
	if x.parent == t.null {
		t.root = y
	} else if x == x.parent.right {
		x.parent.right = y
	} else {
		x.parent.left = y
	}
	y.right = x
	x.parent = y
	y.max = x.max
	x.max = max(x.Interval.High, x.left.max, x.right.max)
}

func (t *IntervalTree) Search(ctx context.Context, i *Interval) (*Interval, interface{}, error) {
	if err := checkIntervalInvalid(i); err != nil {
		helper.Logger.Error(ctx, fmt.Sprintf("Failed to search node in interval tree, err: %v", err))
		return nil, nil, err
	}
	node, err := t.preOrderTree(ctx, i)
	if err != nil {
		helper.Logger.Error(ctx, fmt.Sprintf("Failed to search node in interval tree, err: %v", err))
		return nil, nil, err
	}
	return node.Interval, node.Value, nil
}

func (t *IntervalTree) preOrderTree(ctx context.Context, i *Interval) (*itNode, error){
	x := t.root
	for x != t.null && notOverlap(x.Interval, i) {
		if x.left != t.null && x.left.max >= i.Low {
			x = x.left
		} else {
			x = x.right
		}
	}
	if x == t.null {
		err := ErrIntervalTreeNodeNotExists
		return nil, err
	}
	return x, nil
}

func notOverlap(x, i *Interval) bool {
	if x.High < i.Low || i.High < x.Low {
		return true
	}
	return false
}

func (t *IntervalTree) delete(z *itNode) {
	y := z
	x := t.null
	y_original_color := y.color
	if z.left == t.null {
		x = z.right
		t.transplant(z, z.right)
	} else if z.right == t.null {
		x = z.left
		t.transplant(z, z.left)
	} else {
		y = t.treeMinimum(z.right)
		y_original_color = y.color
		x = y.right
		if y.parent == z {
			x.parent = y						
		} else {
			t.transplant(y, y.right)
			y.right = z.right
			y.right.parent = y
		}
		t.transplant(z, y)
		y.left = z.left
		y.left.parent = y
		y.color = z.color
	}
	k := x.parent
	for k != t.null {
		k.max = max(k.left.max, k.right.max, k.Interval.High)
		k = k.parent
	}
	if y_original_color == black {
		t.deleteFixup(x)
	}
}

func (t *IntervalTree) transplant(u, v *itNode) {
	if u.parent == t.null {
		t.root = v
	} else if u == u.parent.left {
		u.parent.left = v
	} else {
		u.parent.right = v
	}
	v.parent = u.parent
}

func (t *IntervalTree) treeMinimum(x *itNode) *itNode {
	for x.left != t.null {
		x = x.left
	}
	return x
}

func (t *IntervalTree) deleteFixup(x *itNode) {
	for x != t.root && x.color == black {
		if x == x.parent.left {
			w := x.parent.right
			if w.color == red {
				w.color = black
				x.parent.color = red
				t.leftRotate(x.parent)
				w = x.parent.right
			}
			if w.left.color == black && w.right.color == black {
				w.color = red
				x = x.parent
			} else {
				if w.right.color == black {
					w.left.color = black
					w.color = red
					t.rightRotate(w)
					w = x.parent.right
				}
				w.color = x.parent.color
				x.parent.color = black
				w.right.color = black
				t.leftRotate(x.parent)
				x = t.root
			}
		} else {
			w := x.parent.left
			if w.color == red {
				w.color = black
				x.parent.color = red
				t.rightRotate(x.parent)
				w = x.parent.left
			}
			if w.left.color == black && w.right.color == black {
				w.color = red
				x = x.parent
			} else {
				if w.left.color == black {
					w.right.color = black
					w.color = red
					t.leftRotate(w)
					w = x.parent.left
				}
				w.color = x.parent.color
				x.parent.color = black
				w.left.color = black
				t.rightRotate(x.parent)
				x = t.root
			}
		}
	}
	x.color = black
}

func (t *IntervalTree) BatchInsert(ctx context.Context, kvmap map[*Interval]interface{}) error {
	start := time.Now().UTC().UnixNano()
	for k, v := range kvmap {
		err := t.insert(ctx, k, v)
		if err != nil {
			helper.Logger.Error(ctx, fmt.Sprintf("Failed to insert node %v in current batch, err: %v", k, err))
			return err
		}
	}
	end := time.Now().UTC().UnixNano()
	helper.Logger.Info(ctx, fmt.Sprintf("BatchInsert %d nodes, cost time: %d", len(kvmap), end - start))
	return nil
}

func checkInvalidNode(node *itNode) bool {
	if node.Interval == nil || node.Interval.Low > node.Interval.High || node.Value == nil {
		return true
	}
	return false
}

func (t *IntervalTree) BatchDelete(ctx context.Context, intervalList []*Interval) error {
	start := time.Now().UTC().UnixNano()
	for i, value := range intervalList {
		node, err := t.intervalPerfectMatch(ctx, value)
		if err != nil {
			helper.Logger.Error(ctx, fmt.Sprintf("Failed to delete %dth node: %+v in current batch, err: %v", i + 1, value, err))
			return err
		} else {
			t.delete(node)
		}
	}
	end := time.Now().UTC().UnixNano()
	helper.Logger.Info(ctx, fmt.Sprintf("BatchDelete %d nodes, cost time: %d", len(intervalList), end - start))
	return nil
}

func checkIntervalInvalid(i *Interval) error {
	if i == nil || i.Low > i.High {
		return errors.New("Interval is invalid")
	}
	return nil
}

func (t *IntervalTree) intervalPerfectMatch(ctx context.Context, i *Interval) (*itNode, error){
	if err := checkIntervalInvalid(i); err != nil {
		return nil, err
	}
	x := t.root
	for x != t.null && x.Interval.Low != i.Low && x.Interval.High != i.High {		
		if x.Interval.Low > i.Low {
			x = x.left
		} else {
			x = x.right
		}
	}
	if x == t.null {
		err := ErrIntervalTreeNodeNotExists
		helper.Logger.Error(ctx, fmt.Sprintf("Failed to match perfectly the interval with node, err: %v", err))
		return nil, err
	}
	return x, nil
}

type KV struct {
	Interval *Interval
	Value interface{}
}

func (t *IntervalTree) ListNode() (ch chan *KV) {
	ch = make(chan *KV)
	go func() {
		t.inOrder(t.root, ch)
		close(ch)
	}()
	return ch
}

func (t *IntervalTree) inOrder(x *itNode, ch chan *KV) {
	if x != t.null {
		t.inOrder(x.left, ch)
		kv := &KV{
			Interval: x.Interval,
			Value: x.Value,		
		}
		ch <- kv
		t.inOrder(x.right, ch)
	}
}

func (t *IntervalTree) UpdateNode(ctx context.Context, i *Interval, value interface{}) error {
	node, err := t.intervalPerfectMatch(ctx, i)
	if err != nil {
		helper.Logger.Error(ctx, fmt.Sprintf("Failed to update node, err: %v", err))
		return err
	} else {
		node.Value = value
	}
	return nil
}