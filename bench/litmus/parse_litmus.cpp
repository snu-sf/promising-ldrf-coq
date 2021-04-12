#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <string>
#include <cstring>
#include <algorithm>
#include <math.h>

using namespace std;

const int schemes = 3;
const string bins[] = { "main", "main.fake", "main.cmp" };
const string names[] = { "ref", "fake", "cmp" };

int main(int argc, char** argv) {
  if (argc != 7) {
    cout << "usage: " << argv[0] << " dir filename outdir runs discard" << endl;
    exit(1);
  }

  string dir = string(argv[1]);
  string kind = string(argv[2]);
  int min = std::stoi(argv[3]);
  int max = std::stoi(argv[4]);
  int runs = std::stoi(argv[5]);
  int discarded = std::stoi(argv[6]);
  int size = runs - 2 * discarded;

  ofstream outfile;
  outfile.open(dir + "/out/" + kind + "_stat.csv");

  int threads = 0;
  outfile << "threads,";
  for (int i = min; i <= max; i*=2) {
    outfile << i << ",,,";
    threads++;
  }
  outfile << endl;

  outfile << "scheme,";
  for (int i = 0; i < threads; i++) {
    for (int j = 0; j < schemes; j++) {
      outfile << names[j] << ",";
    }
  }
  outfile << endl;

  double** results[schemes];
  for (int i = 0; i < schemes; i++) {
    double** arr = new double*[threads];
    for (int j = 0; j < threads; j++) {
      arr[j] = new double[runs];
    }
    results[i] = arr;
  }

  double* means[schemes];
  for (int i = 0; i < schemes; i++) {
    means[i] = new double[threads];
  }

  double* stdevs[schemes];
  for (int i = 0; i < schemes; i++) {
    stdevs[i] = new double[threads];
  }

  int n = 0;
  for (int i = min; i <= max; i*=2) {
    for (int j = 0; j < schemes; j++) {
      ifstream infile;
      infile.open(dir + "/" + bins[j] + "-" + kind + "-" + to_string(i) + "-" + "4000000" + ".txt");
      if (infile.fail()) {
        infile.close();
        infile.open(dir + "/" + bins[j] + "-" + kind + "-" + to_string(i) + "-" + "40000000" + ".txt");
      }

      for (int k = 0; k < runs; k++) {
        double time;
        infile >> time;
        results[j][n][k] = time;
      }
      sort(results[j][n], results[j][n] + runs);

      double sum = 0;
      double sumsquare = 0;
      for (int k = discarded; k < runs - discarded; k++) {
        double time = results[j][n][k];
        sum += time;
        sumsquare += time * time;
      }

      means[j][n] = sum / size;
      stdevs[j][n] = sqrt(sumsquare/(size - 1) - sum * sum / size / (size - 1));
      infile.close();
    }
    n++;
  }

  outfile << "average,";
  for (int i = 0; i < threads; i++) {
    for (int j = 0; j < schemes; j++) {
      outfile << means[j][i] << ",";
    }
  }
  outfile << endl;

  outfile << "stdev,";
  for (int i = 0; i < threads; i++) {
    for (int j = 0; j < schemes; j++) {
      outfile << stdevs[j][i] << ",";
    }
  }
  outfile << endl;

  outfile << "normalized_average,";
  for (int i = 0; i < threads; i++) {
    for (int j = 0; j < schemes; j++) {
      outfile << (means[j][i] / means[0][i]) << ",";
    }
  }
  outfile << endl;

  outfile << "normalized_stdev,";
  for (int i = 0; i < threads; i++) {
    for (int j = 0; j < schemes; j++) {
      outfile << (stdevs[j][i] / means[0][i]) << ",";
    }
  }
  outfile << endl;

  outfile.close();
  return 0;
}
