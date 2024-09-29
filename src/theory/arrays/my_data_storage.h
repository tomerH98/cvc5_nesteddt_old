
#ifndef CVC5__NESTEDDT__MY_DATA_STORAGE_H
#define CVC5__NESTEDDT__MY_DATA_STORAGE_H

#include "cvc5_private.h"
#include "expr/dtype.h" 
#include "cvc5/cvc5.h"
#include <map>
#include <vector>

namespace cvc5::internal {

struct ArrayStruct
{
    std::set<Node> seenArrays;       // Vector of nodes called seenArrays
    std::map<Node, int> orderedIndexes; // Map from nodes to int called orderedIndexes
    Node consToArr;                     // Node called consToArr
    Node arrToCons;                     // Node called arrToCons
};

class MyDataStorage
{
 public:
  static MyDataStorage& getInstance()
  {
    static MyDataStorage instance;
    return instance;
  }

  // Destructor to clear data before NodeManager is destroyed
  ~MyDataStorage()
  {
    arrInfo.clear();
  }

  // Delete copy constructor and assignment operator
  MyDataStorage(const MyDataStorage&) = delete;
  MyDataStorage& operator=(const MyDataStorage&) = delete;

  // Public data structures
  std::map<TypeNode, ArrayStruct> arrInfo;
  int check = 0;
  // Add other data structures as needed

 private:
  // Private constructor
  MyDataStorage() {}
};
 // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__NESTEDDT__MY_DATA_STORAGE_H */