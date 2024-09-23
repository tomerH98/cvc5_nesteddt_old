// File: src/theory/nesteddt/my_data_storage.h

#ifndef CVC5__NESTEDDT__MY_DATA_STORAGE_H
#define CVC5__NESTEDDT__MY_DATA_STORAGE_H

#include "cvc5_private.h"
#include "expr/dtype.h" 
#include "cvc5/cvc5.h"
#include <map>
#include <vector>

namespace cvc5::internal {

class MyDataStorage
{
 public:
  static MyDataStorage& getInstance()
  {
    static MyDataStorage instance;
    return instance;
  }

  // Delete copy constructor and assignment operator
  MyDataStorage(const MyDataStorage&) = delete;
  MyDataStorage& operator=(const MyDataStorage&) = delete;

  // Public data structures
  std::map<TypeNode, DType> d_mapDType;
  std::map<TypeNode, TypeNode> d_resolvedMap;
  int check = 0;
  // Add other data structures as needed

 private:
  // Private constructor
  MyDataStorage() {}
};
 // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__NESTEDDT__MY_DATA_STORAGE_H */
