class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next

def reverse_list(head):
    prev = None
    current = head
    while current:
        next_node = current.next
        current.next = prev
        prev = current
        current = next_node
    return prev

# Test the code (Example)
if __name__ == "__main__":
    # Create a linked list: 1 → 2 → 3 → None
    node3 = ListNode(3)
    node2 = ListNode(2, node3)
    node1 = ListNode(1, node2)
    
    reversed_head = reverse_list(node1)
    # Now reversed_head is 3 → 2 → 1 → None