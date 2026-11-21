License Apache-2.0 Takeo Yamamoto
#include <cstddef>
#include <cstdint>
#include <cuda_runtime.h>

namespace fast_cuda {

// 述語 Pred に合致する入力要素だけを出力配列へ詰めるカーネル
// 出力スロットの確保はワープ単位（最大32スレッド）で1回の atomicAdd に集約する
template <typename T, typename Pred>
__global__ void warp_stream_compact_kernel(
    const T* __restrict__ input,
    std::size_t n,
    T* __restrict__ output,
    unsigned long long* __restrict__ out_count,
    Pred pred) {
  constexpr unsigned int kFullMask = 0xffffffffu;
  const std::size_t idx = static_cast<std::size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  const unsigned int lane = threadIdx.x & 31u;

  bool keep = false;
  T val{};
  if (idx < n) {
    val = input[idx];
    keep = pred(val);
  }

  // ワープ内で keep == true のスレッドのビットマスクを取得
  const unsigned int active_mask = __activemask();
  const unsigned int vote_mask = __ballot_sync(active_mask, keep ? 1u : 0u);
  const unsigned int warp_total = __popc(vote_mask);

  // このワープで出力する要素が1つ以上ある場合のみ、レーン0がまとめてスロットを確保
  unsigned long long warp_base = 0ULL;
  if (warp_total > 0u) {
    if (lane == 0u) {
      warp_base = atomicAdd(out_count, static_cast<unsigned long long>(warp_total));
    }
    warp_base = __shfl_sync(active_mask, warp_base, 0);
  }

  // 自分のレーンより下位にある採用要素数を数えて、ワープ内オフセットを確定
  if (keep) {
    const unsigned int lower_mask = (lane == 0u) ? 0u : (kFullMask >> (32u - lane));
    const unsigned int local_offset = __popc(vote_mask & lower_mask);
    output[warp_base + local_offset] = val;
  }
}

// ランチャ関数：ホスト側から呼び出しやすいラッパー
template <typename T, typename Pred>
cudaError_t launch_warp_stream_compact(
    const T* d_input,
    std::size_t n,
    T* d_output,
    unsigned long long* d_out_count,
    Pred pred,
    cudaStream_t stream = nullptr) {
  if (n == 0) {
    return cudaMemsetAsync(d_out_count, 0, sizeof(unsigned long long), stream);
  }

  cudaError_t err = cudaMemsetAsync(d_out_count, 0, sizeof(unsigned long long), stream);
  if (err != cudaSuccess) {
    return err;
  }

  constexpr int kThreadsPerBlock = 256;
  const std::size_t blocks = (n + kThreadsPerBlock - 1) / kThreadsPerBlock;
  warp_stream_compact_kernel<<<static_cast<unsigned int>(blocks), kThreadsPerBlock, 0, stream>>>(
      d_input, n, d_output, d_out_count, pred);

  return cudaGetLastError();
}

} // namespace fast_cuda
