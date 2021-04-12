#include <iostream>
#include <iomanip>
#include <chrono>
#include <string>
#include <thread>
#include <vector>

#include "incr.h"

using namespace std;
using msec = std::chrono::duration<double, std::milli>;


int main(int argc, char** argv) {
  if (argc != 4) {
    cout << "usage: " << argv[0] << " test_kind n_threads n_op" << endl;
    exit(1);
  }

  int kind = stoi(argv[1]);
  int n_threads = stoi(argv[2]);
  int n_op = stoi(argv[3]);
  int n_op_per_thread = n_op / n_threads;

  vector<thread*> threads;

  const auto start = chrono::system_clock::now();

  switch(kind) {
    case 1:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(incr, n_op_per_thread));
      break;
    case 2:
      for (int i = 0; i < n_threads; i++) {
        if (i % 2 == 0)
          threads.emplace_back(new thread(incr_load, n_op_per_thread));
        else
          threads.emplace_back(new thread(incr_store, n_op_per_thread));
      }
      break;
    case 3:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(xchg, n_op_per_thread));
      break;
    case 4:
      for (int i = 0; i < n_threads; i++) {
        if (i % 2 == 0)
          threads.emplace_back(new thread(xchg_load, n_op_per_thread));
        else
          threads.emplace_back(new thread(xchg_store, n_op_per_thread));
      }
      break;
    case 5:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(load, n_op_per_thread));
      break;
    case 6:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(load_store, n_op_per_thread));
      break;
    case 7:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(load_unroll, n_op_per_thread));
      break;
    case 8:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(load_store_unroll, n_op_per_thread));
      break;
    case 9:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(incr_unroll, n_op_per_thread));
      break;
    case 10:
      for (int i = 0; i < n_threads; i++) {
        if (i % 2 == 0)
          threads.emplace_back(new thread(incr_load_unroll, n_op_per_thread));
        else
          threads.emplace_back(new thread(incr_store_unroll, n_op_per_thread));
      }
      break;
    case 11:
      for (int i = 0; i < n_threads; i++)
        threads.emplace_back(new thread(xchg_unroll, n_op_per_thread));
      break;
    case 12:
      for (int i = 0; i < n_threads; i++) {
        if (i % 2 == 0)
          threads.emplace_back(new thread(xchg_load_unroll, n_op_per_thread));
        else
          threads.emplace_back(new thread(xchg_store_unroll, n_op_per_thread));
      }
      break;
    default:
      cout << "Wrong test" << endl;
      exit(1);
  }

  for (auto &th: threads)
    th->join();

  const auto end = chrono::system_clock::now();

  cout << fixed << setprecision(4);
  cout << msec(end - start).count() << endl;

  return 0;
}
