int mean = low + (high -low) / 2;
//@ assert low <= mean <= high;
 if (arr[mean] == query)
 //@ for not_exists: assert \false;
