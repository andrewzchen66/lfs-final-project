shape:
  selector: CommitNode
  value: circle
color:
  - selector: Root
    value: '#4B0082'
  - selector: CommitNode
    value: '#98F998'
label:
  - selector: CommitNode
    text: n.fileState
size:
  selector: CommitNode
  value: 25
edge:
  - selector: next
    style: straight
    orientation: below
    length: 20
  - selector: unusedCommits
    style: straight
    orientation: below
    length: 20
  - selector: outgoingBranches
    style: straight
    orientation: directlyRight
    length: 20
  - selector: prevBranchNode
    style: straight
    orientation: directlyLeft
    length: 20
constraints:
  - orientation:
      selector: next
      directions:
        - directlyBelow
    spacing: 20
  - orientation:
      selector: unusedCommits
      directions:
        - below
    spacing: 20
  - orientation:
      selector: outgoingBranches
      directions:
        - directlyRight
    spacing: 20
  - orientation:
      selector: prevBranchNode
      directions:
        - directlyLeft
      spacing: 20
directives:
  - flag: hideDisconnectedBuiltIns
  - style: edge.arrowSize=0.5
  - style: node.fontSize=10
  - style: levelSeparation=50
  - style: nodeSpacing=40
  - style: edge.curvature=0





