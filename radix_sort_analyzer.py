"""
Radix Sort Implementation for Network Packet Size Analysis of Security Logs
with comprehensive complexity analysis, input validation, and security features.

This module provides tools for sorting and analyzing network packet data
using Radix Sort algorithm, which is particularly efficient for integers
like network packet sizes.
"""

import time
import random
import math
from typing import List, Dict, Any, Union, Tuple


class SecurityPacket:
    """
    Represents a network packet with security-relevant attributes
    """
    def __init__(self, size: int, source_ip: str, destination_ip: str, 
                 protocol: str, timestamp: float):
        """
        Initialize a security packet
        
        Args:
            size: Size of the packet in bytes
            source_ip: Source IP address
            destination_ip: Destination IP address
            protocol: Protocol used (e.g., TCP, UDP, ICMP)
            timestamp: Unix timestamp when packet was captured
        """
        self.size = size
        self.source_ip = source_ip
        self.destination_ip = destination_ip
        self.protocol = protocol
        self.timestamp = timestamp
    
    def __repr__(self) -> str:
        return (f"SecurityPacket(size={self.size}, src={self.source_ip}, "
                f"dst={self.destination_ip}, proto={self.protocol})")


class PacketAnalyzer:
    """
    Analyzer for network packets using Radix Sort for efficient processing
    """
    def __init__(self):
        self.packets = []
        self.sorted_by_size = False
        self.performance_metrics = {}
    
    def load_packets(self, packets: List[SecurityPacket]) -> None:
        """
        Load packets into the analyzer
        
        Args:
            packets: List of SecurityPacket objects
        """
        # Security check: Validate input
        if not isinstance(packets, list):
            raise ValueError("Packets must be provided as a list")
        
        if not all(isinstance(p, SecurityPacket) for p in packets):
            raise TypeError("All elements must be SecurityPacket instances")
        
        self.packets = packets
        self.sorted_by_size = False
    
    def sort_by_size(self) -> List[SecurityPacket]:
        """
        Sort packets by size using Radix Sort
        
        Returns:
            Sorted list of packets
        """
        if not self.packets:
            return []
        
        # Extract sizes for sorting
        sizes = [packet.size for packet in self.packets]
        packet_map = {i: packet for i, packet in enumerate(self.packets)}
        
        # Create index array
        indices = list(range(len(sizes)))
        
        # Time the sorting operation for performance analysis
        start_time = time.time()
        
        # Sort indices based on corresponding sizes
        sorted_indices = self._radix_sort_indices(sizes, indices)
        
        # Rearrange packets based on sorted indices
        sorted_packets = [packet_map[i] for i in sorted_indices]
        
        # Record performance metrics
        elapsed_time = time.time() - start_time
        self.performance_metrics = {
            "sort_time": elapsed_time,
            "packets_count": len(self.packets),
            "algorithm": "radix_sort",
            "theoretical_complexity": f"O(n * k) where n={len(sizes)} and k=digits"
        }
        
        self.packets = sorted_packets
        self.sorted_by_size = True
        
        return sorted_packets
    
    def _radix_sort_indices(self, values: List[int], indices: List[int]) -> List[int]:
        """
        Perform Radix Sort on indices based on corresponding values
        
        Args:
            values: List of values to sort by
            indices: List of indices to be sorted
            
        Returns:
            Sorted list of indices
        """
        # Input validation
        if not values:
            return []
        
        # Find maximum number to determine number of digits
        max_value = max(values)
        
        # Perform counting sort for every digit 
        exp = 1
        while max_value // exp > 0:
            indices = self._counting_sort_indices(values, indices, exp)
            exp *= 10
            
        return indices
    
    def _counting_sort_indices(self, values: List[int], indices: List[int], exp: int) -> List[int]:
        """
        Counting sort implementation for Radix Sort that sorts indices
        
        Args:
            values: Values to sort by
            indices: Indices to be sorted
            exp: Current digit position
            
        Returns:
            Sorted indices for current digit position
        """
        n = len(indices)
        output = [0] * n
        count = [0] * 10  # Digits 0-9
        
        # Count occurrences of each digit
        for i in range(n):
            idx = indices[i]
            digit = (values[idx] // exp) % 10
            count[digit] += 1
        
        # Update count to store actual position of this digit in output
        for i in range(1, 10):
            count[i] += count[i - 1]
        
        # Build the output array
        for i in range(n - 1, -1, -1):
            idx = indices[i]
            digit = (values[idx] // exp) % 10
            output[count[digit] - 1] = idx
            count[digit] -= 1
            
        return output
    
    def analyze_size_distribution(self) -> Dict[str, Any]:
        """
        Analyze the packet size distribution
        
        Returns:
            Dictionary with distribution statistics
        """
        if not self.sorted_by_size:
            self.sort_by_size()
            
        sizes = [packet.size for packet in self.packets]
        
        if not sizes:
            return {"error": "No packets to analyze"}
            
        # Basic statistics
        min_size = min(sizes)
        max_size = max(sizes)
        avg_size = sum(sizes) / len(sizes)
        median_size = sizes[len(sizes) // 2]  # Assumes already sorted
        
        # Size distribution analysis
        size_ranges = {
            "small": 0,      # < 100 bytes
            "medium": 0,     # 100-1000 bytes
            "large": 0,      # 1000-1500 bytes
            "jumbo": 0       # > 1500 bytes
        }
        
        for size in sizes:
            if size < 100:
                size_ranges["small"] += 1
            elif size < 1000:
                size_ranges["medium"] += 1
            elif size <= 1500:
                size_ranges["large"] += 1
            else:
                size_ranges["jumbo"] += 1
                
        # Convert to percentages
        for key in size_ranges:
            size_ranges[key] = (size_ranges[key] / len(sizes)) * 100
            
        return {
            "min_size": min_size,
            "max_size": max_size,
            "avg_size": avg_size,
            "median_size": median_size,
            "size_distribution": size_ranges,
            "total_packets": len(sizes)
        }
    
    def detect_anomalies(self) -> List[SecurityPacket]:
        """
        Detect anomalous packets based on size
        
        Returns:
            List of suspicious packets
        """
        if not self.sorted_by_size:
            self.sort_by_size()
            
        sizes = [packet.size for packet in self.packets]
        
        if len(sizes) < 2:
            return []
            
        # Calculate statistics for anomaly detection
        mean = sum(sizes) / len(sizes)
        variance = sum((x - mean) ** 2 for x in sizes) / len(sizes)
        std_dev = math.sqrt(variance)
        
        # Define threshold for anomalies (packets > 2 standard deviations from mean)
        upper_threshold = mean + 2 * std_dev
        lower_threshold = max(0, mean - 2 * std_dev)  # Prevent negative threshold
        
        # Find anomalous packets
        anomalies = [
            packet for packet in self.packets
            if packet.size > upper_threshold or packet.size < lower_threshold
        ]
        
        return anomalies
    
    def get_performance_analysis(self) -> Dict[str, Any]:
        """
        Get detailed performance analysis of the sorting operation
        
        Returns:
            Dictionary with performance metrics and complexity analysis
        """
        if not self.performance_metrics:
            return {"error": "No sorting operation performed yet"}
            
        # Add theoretical vs. actual performance analysis
        n = self.performance_metrics.get("packets_count", 0)
        
        # Extend the performance metrics with complexity analysis
        analysis = {
            **self.performance_metrics,
            "space_complexity": "O(n + k) where k=10 for decimal digits",
            "time_complexity_details": {
                "best_case": "O(n * k) - always",
                "average_case": "O(n * k) - always",
                "worst_case": "O(n * k) - always"
            },
            "comparison": {
                "vs_quicksort": "More efficient for small range of values",
                "vs_mergesort": "Better space complexity than merge sort's O(n)",
                "vs_heapsort": "Often faster when range of keys is limited"
            },
            "stability": "Stable sort algorithm",
            "parallelization": "Can be parallelized for large datasets"
        }
        
        return analysis


def radix_sort(arr: List[int]) -> List[int]:
    """
    Implementation of Radix Sort algorithm for integers
    
    Args:
        arr: List of integers to sort
        
    Returns:
        Sorted list
    """
    # Security check: Validate input to prevent malicious data
    if not isinstance(arr, list):
        raise ValueError("Input must be a list of integers")
    
    if not arr:
        return []
    
    # Verify all elements are integers
    if not all(isinstance(x, int) for x in arr):
        raise TypeError("All elements must be integers")
    
    # Detect if any negative numbers are present
    has_negatives = any(x < 0 for x in arr)
    
    if has_negatives:
        # Split into negative and non-negative parts
        neg = [abs(x) for x in arr if x < 0]
        pos = [x for x in arr if x >= 0]
        
        # Sort both parts separately
        sorted_neg = radix_sort_positive(neg)
        sorted_pos = radix_sort_positive(pos)
        
        # Combine results: reversed negatives (now made positive) followed by positives
        return [-x for x in reversed(sorted_neg)] + sorted_pos
    else:
        return radix_sort_positive(arr)


def radix_sort_positive(arr: List[int]) -> List[int]:
    """
    Radix Sort implementation for positive integers
    
    Args:
        arr: List of positive integers
        
    Returns:
        Sorted list
    """
    if not arr:
        return []
    
    # Find maximum number to determine number of digits
    max_num = max(arr)
    exp = 1
    
    # Do counting sort for every digit
    while max_num // exp > 0:
        counting_sort(arr, exp)
        exp *= 10
        
    return arr


def counting_sort(arr: List[int], exp: int) -> None:
    """
    Counting sort implementation for a specific digit
    
    Args:
        arr: Array to be sorted
        exp: Current digit place value
    """
    n = len(arr)
    output = [0] * n
    count = [0] * 10  # Digits 0-9
    
    # Store count of occurrences of current digit
    for i in range(n):
        index = (arr[i] // exp) % 10
        count[index] += 1
    
    # Change count[i] to contain actual position of this digit in output[]
    for i in range(1, 10):
        count[i] += count[i - 1]
    
    # Build the output array
    i = n - 1
    while i >= 0:
        index = (arr[i] // exp) % 10
        output[count[index] - 1] = arr[i]
        count[index] -= 1
        i -= 1
    
    # Copy the output array to arr[] so that arr[] contains sorted numbers
    for i in range(n):
        arr[i] = output[i]


def analyze_algorithm_complexity() -> Dict[str, str]:
    """
    Analyze the time and space complexity of Radix Sort
    
    Returns:
        Dictionary with complexity analysis
    """
    return {
        "time_complexity": {
            "best_case": "O(n * k) where n is number of elements and k is number of digits",
            "average_case": "O(n * k)",
            "worst_case": "O(n * k)"
        },
        "space_complexity": "O(n + k) where k is radix (10 for decimal)",
        "stability": "Stable",
        "comparison_based": "No - Radix sort is not comparison-based",
        "in_place": "No - Requires additional memory",
        "advantages": [
            "Fast when the range of values is limited",
            "Works well for fixed-length integers like IP addresses or packet sizes",
            "Stable sorting algorithm (maintains relative order of equal elements)"
        ],
        "disadvantages": [
            "Not very efficient for wide ranges of values",
            "Requires additional memory",
            "Not as adaptive as comparison-based sorts"
        ]
    }


def benchmark_sorting(array_size: int = 10000, iterations: int = 5) -> Dict[str, float]:
    """
    Benchmark the performance of Radix Sort
    
    Args:
        array_size: Size of the array to sort
        iterations: Number of iterations for averaging
        
    Returns:
        Dictionary with benchmark results
    """
    results = {"radix_sort": 0.0}
    
    for _ in range(iterations):
        # Generate random array
        arr = [random.randint(1, 100000) for _ in range(array_size)]
        
        # Benchmark radix sort
        start_time = time.time()
        radix_sort(arr.copy())
        results["radix_sort"] += (time.time() - start_time)
    
    # Calculate averages
    results["radix_sort"] /= iterations
    
    return results


def generate_test_packets(count: int = 100) -> List[SecurityPacket]:
    """
    Generate test packets for analysis
    
    Args:
        count: Number of packets to generate
        
    Returns:
        List of SecurityPacket objects
    """
    protocols = ["TCP", "UDP", "ICMP", "HTTP", "HTTPS"]
    
    # Common packet sizes with focus on common MTUs and some anomalies
    common_sizes = [64, 128, 256, 512, 576, 1024, 1280, 1460, 1500, 9000]
    weights = [0.1, 0.1, 0.1, 0.15, 0.05, 0.15, 0.05, 0.2, 0.05, 0.05]  # Probabilities
    
    packets = []
    current_time = time.time()
    
    for i in range(count):
        # Generate random source and destination IPs
        src_ip = f"192.168.{random.randint(0, 255)}.{random.randint(1, 254)}"
        dst_ip = f"10.0.{random.randint(0, 255)}.{random.randint(1, 254)}"
        
        # Select protocol
        protocol = random.choice(protocols)
        
        # Generate packet size with weighted probabilities for realism
        # Either choose from common sizes or generate a truly random one
        if random.random() < 0.9:  # 90% common sizes
            size = random.choices(common_sizes, weights=weights, k=1)[0]
        else:  # 10% random sizes
            size = random.randint(40, 10000)
        
        # Add some variation to common sizes
        if random.random() < 0.3:  # 30% chance of slight variation
            size += random.randint(-10, 10)
        
        # Create the packet with a sequential timestamp
        timestamp = current_time + i * 0.001  # 1ms between packets
        packets.append(SecurityPacket(size, src_ip, dst_ip, protocol, timestamp))
    
    return packets


# Example: Sort packet sizes in a network log
if __name__ == "__main__":
    print("Network Packet Size Analysis using Radix Sort\n")
    
    # Basic radix sort example
    packet_sizes = [1500, 45, 1024, 78, 512, 9000]  # Common MTU sizes + outliers
    print("Original packet sizes:", packet_sizes)
    sorted_packets = radix_sort(packet_sizes)
    print("Sorted (ascending):", sorted_packets)
    
    # Generate test packets
    print("\nGenerating test network packets for analysis...")
    test_packets = generate_test_packets(1000)
    print(f"Generated {len(test_packets)} test packets")
    
    # Create analyzer and load packets
    analyzer = PacketAnalyzer()
    analyzer.load_packets(test_packets)
    
    # Sort packets by size
    print("\nSorting packets by size using Radix Sort...")
    sorted_packets = analyzer.sort_by_size()
    print(f"First 5 packets (smallest): {sorted_packets[:5]}")
    print(f"Last 5 packets (largest): {sorted_packets[-5:]}")
    
    # Analyze size distribution
    print("\nAnalyzing packet size distribution...")
    distribution = analyzer.analyze_size_distribution()
    print(f"Min size: {distribution['min_size']} bytes")
    print(f"Max size: {distribution['max_size']} bytes")
    print(f"Average size: {distribution['avg_size']:.2f} bytes")
    print(f"Size distribution:")
    for category, percentage in distribution['size_distribution'].items():
        print(f"  {category}: {percentage:.1f}%")
    
    # Detect anomalies
    print("\nDetecting anomalous packets...")
    anomalies = analyzer.detect_anomalies()
    print(f"Found {len(anomalies)} anomalous packets")
    if anomalies:
        print("First 3 anomalies:")
        for i, packet in enumerate(anomalies[:3]):
            print(f"  {i+1}. {packet}")
    
    # Get performance analysis
    print("\nPerformance Analysis:")
    performance = analyzer.get_performance_analysis()
    print(f"Sort time: {performance['sort_time']:.6f} seconds")
    print(f"Algorithm: {performance['algorithm']}")
    print(f"Theoretical time complexity: {performance['theoretical_complexity']}")
    print(f"Space complexity: {performance['space_complexity']}")
    print("Comparison with other algorithms:")
    for algo, comparison in performance['comparison'].items():
        print(f"  {algo}: {comparison}")
    
    # Algorithm complexity analysis
    print("\nRadix Sort Algorithm Analysis:")
    complexity = analyze_algorithm_complexity()
    print("Time Complexity:")
    for case, analysis in complexity['time_complexity'].items():
        print(f"  {case}: {analysis}")
    print(f"Space Complexity: {complexity['space_complexity']}")
    print(f"Is comparison-based? {complexity['comparison_based']}")
    print(f"Is in-place? {complexity['in_place']}")
    
    # Run benchmark
    print("\nBenchmarking Radix Sort...")
    benchmark = benchmark_sorting(array_size=50000, iterations=3)
    print(f"Average time for sorting 50,000 elements: {benchmark['radix_sort']:.6f} seconds")
