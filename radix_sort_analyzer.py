"""
Radix Sort Implementation for Network Packet Size Analysis of Security Log
"""
def radix_sort(arr):
    # Security check: Validate input to prevent malicious data
    if not isinstance(arr, list):
        raise ValueError("Input must be a list of integers")
    
    max_num = max(arr) if arr else 0
    exp = 1
    while max_num // exp > 0:
        counting_sort(arr, exp)
        exp *= 10
    return arr

def counting_sort(arr, exp):
    n = len(arr)
    output = [0] * n
    count = [0] * 10

    for i in range(n):
        index = (arr[i] // exp) % 10
        count[index] += 1

    for i in range(1, 10):
        count[i] += count[i - 1]

    i = n - 1
    while i >= 0:
        index = (arr[i] // exp) % 10
        output[count[index] - 1] = arr[i]
        count[index] -= 1
        i -= 1

    for i in range(n):
        arr[i] = output[i]

# Example: Sort packet sizes (in bytes) in a network log
if __name__ == "__main__":
    packet_sizes = [1500, 45, 1024, 78, 512, 9000]  # Common MTU sizes + outliers
    print("Original packet sizes:", packet_sizes)
    sorted_packets = radix_sort(packet_sizes)
    print("Sorted (ascending):", sorted_packets)
