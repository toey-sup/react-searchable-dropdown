import * as React from 'react';
import { FixedSizeList as List, FixedSizeListProps } from 'react-window';

interface ListProps extends Readonly<FixedSizeListProps<any>> {
  outerId: string;
  innerId: string;
}

function ListWithId({
  outerId, innerId, outerElementType, innerElementType, ...props
}: ListProps, ref: React.ForwardedRef<List<any>>) {
  const outerElementTypeWithId = React.useMemo(() => {
    if (outerId === undefined) return outerElementType;
    return React.forwardRef((curProps, curref) => React.createElement(outerElementType || 'div', {
      ref: curref,
      id: outerId,
      ...curProps,
    }));
  }, [outerId, outerElementType]);
  const innerElementTypeWithId = React.useMemo(() => {
    if (innerId === undefined) return innerElementType;
    return React.forwardRef((curProps, curref) => React.createElement(innerElementType || 'div', {
      ref: curref,
      id: innerId,
      ...curProps,
    }));
  }, [innerId, innerElementType]);
  return (
    <List
      ref={ref}
      outerElementType={outerElementTypeWithId}
      innerElementType={innerElementTypeWithId}
      {...props}
    />
  );
}

export default React.forwardRef(ListWithId);
