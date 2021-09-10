import { useState, useEffect } from 'react';

const useDebounce = (value: any, delay: number = 1000): any => {
  const [debouncedValue, setDebouncedValue] = useState<any>(value);

  useEffect(
    () => {
      const handler = setTimeout(() => {
        setDebouncedValue(value);
      }, delay);
      return () => {
        clearTimeout(handler);
      };
    },
    [value, delay],
  );

  return debouncedValue;
};

export default useDebounce;
