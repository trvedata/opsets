from pyDatalog import pyDatalog

pyDatalog.create_terms('Anc, Child, Child1, Child2, ID, Later, Next, Parent, Prev, Start, Value, child, firstChild, hasChild, hasNextSibling, insert, later2Sibling, laterChild, laterSibling, listElem, nextElem, nextSibling, sibling, siblinglessAncestor')

listElem(ID) <= insert(Parent, ID, Value)
hasChild(Parent) <= insert(Parent, Child, Value)
child(Parent, Child) <= insert(Parent, Child, Value)
laterChild(Parent, Child) <= child(Parent, Prev) & child(Parent, Child) & (Child < Prev)
firstChild(Parent, Child) <= child(Parent, Child) & ~laterChild(Parent, Child)
sibling(Child1, Child2) <= child(Parent, Child1) & child(Parent, Child2)
laterSibling(Prev, Later) <= sibling(Prev, Later) & (Later < Prev)
later2Sibling(Prev, Later) <= sibling(Prev, Next) & sibling(Prev, Later) & (Later < Next) & (Next < Prev)
nextSibling(Prev, Next) <= laterSibling(Prev, Next) & ~later2Sibling(Prev, Next)
hasNextSibling(Prev) <= laterSibling(Prev, Next)
siblinglessAncestor(Start, Start) <= listElem(Start) & ~hasNextSibling(Start)
siblinglessAncestor(Start, Next) <= siblinglessAncestor(Start, Prev) & child(Next, Prev) & ~hasNextSibling(Next)
nextElem(Prev, Next) <= firstChild(Prev, Next)
nextElem(Prev, Next) <= listElem(Prev) & ~hasChild(Prev) & nextSibling(Prev, Next)
nextElem(Prev, Next) <= listElem(Prev) & ~hasChild(Prev) & siblinglessAncestor(Prev, Anc) & child(Parent, Anc) & nextSibling(Parent, Next)

+insert('head', 'a', 'a')
+insert('head', 'b', 'b')
+insert('a', 'a1', 'a1')
+insert('b', 'b1', 'b1')
+insert('b1', 'b2', 'b2')
+insert('b2', 'b3', 'b3')

print (nextElem('head',Next)) # 'b'
print (nextElem('b',Next))    # 'b1'
print (nextElem('b1',Next))   # 'b2'
print (nextElem('b2',Next))   # 'b3'
print (nextElem('b3',Next))   # 'a'
print (nextElem('a',Next))    # 'a1'
print (nextElem('a1',Next))   # []
