License Apache-2.0 Takeo Yamamoto
#include <atomic>
#include <concepts>
#include <cstddef>
#include <new>
#include <optional>
#include <type_traits>
#include <utility>

namespace fast_ipc {

#if defined(__cpp_lib_hardware_interference_size)
inline constexpr std::size_t kCacheLineSize = std::hardware_destructive_interference_size;
#else
inline constexpr std::size_t kCacheLineSize = 64;
#endif

// 単一生産者・単一消費者（SPSC）用の固定長ロックフリーリングバッファ
// Capacity は 2 の累乗を指定し、ビットマスクで剰余演算を回避する
template <typename T, std::size_t Capacity>
  requires(Capacity >= 2 && (Capacity & (Capacity - 1)) == 0 &&
           std::is_nothrow_move_constructible_v<T> &&
           std::is_nothrow_destructible_v<T>)
class SpscRingBuffer {
public:
  SpscRingBuffer() noexcept = default;

  ~SpscRingBuffer() noexcept {
    while (pop().has_value()) {
    }
  }

  SpscRingBuffer(const SpscRingBuffer&) = delete;
  SpscRingBuffer& operator=(const SpscRingBuffer&) = delete;

  template <typename U>
    requires std::constructible_from<T, U> && std::is_nothrow_constructible_v<T, U>
  [[nodiscard]] bool push(U&& value) noexcept {
    const std::size_t head = head_.load(std::memory_order_relaxed);
    const std::size_t tail = tail_.load(std::memory_order_acquire);
    const std::size_t next_head = (head + 1) & kMask;

    if (next_head == tail) {
      return false; // 満杯
    }

    new (slot_ptr(head)) T(std::forward<U>(value));
    head_.store(next_head, std::memory_order_release);
    return true;
  }

  [[nodiscard]] std::optional<T> pop() noexcept {
    const std::size_t tail = tail_.load(std::memory_order_relaxed);
    const std::size_t head = head_.load(std::memory_order_acquire);

    if (tail == head) {
      return std::nullopt; // 空
    }

    T* ptr = slot_ptr(tail);
    std::optional<T> result(std::move(*ptr));
    ptr->~T();

    tail_.store((tail + 1) & kMask, std::memory_order_release);
    return result;
  }

  [[nodiscard]] bool empty() const noexcept {
    return head_.load(std::memory_order_acquire) ==
           tail_.load(std::memory_order_acquire);
  }

private:
  static constexpr std::size_t kMask = Capacity - 1;

  struct alignas(T) StorageSlot {
    alignas(T) std::byte bytes[sizeof(T)];
  };

  [[nodiscard]] T* slot_ptr(std::size_t index) noexcept {
    return std::launder(reinterpret_cast<T*>(&buffer_[index]));
  }

  alignas(kCacheLineSize) std::atomic<std::size_t> head_{0};
  alignas(kCacheLineSize) std::atomic<std::size_t> tail_{0};
  alignas(kCacheLineSize) StorageSlot buffer_[Capacity]{};
};

} // namespace fast_ipc
