import React, { useState, useCallback, useRef } from 'react';
import SelectorPopup, { SearchTextFieldInputProps, SearchTextFieldProps } from './SelectorPopup';
import { ChoiceSection, Choice } from './SectionItem';
import SelectButton from '../SelectButton';

export interface SelectorProps {
  label: string;
  popUpKey: string;
  choiceSections: ChoiceSection[];
  style?: React.CSSProperties;
  className?: string;
  selectDivClassName?: string;
  selectDivPropsStyle?: React.CSSProperties;
  handleSelect: ({ value, name }: { value: Choice; name: string }) => void;
  name?: string;
  error?: boolean;
  placeholder?: string;
  disable?: boolean;
  id?: string;
  disablePortal?: boolean;
  itemHeight?: number;
  scrollDivHeight?: number;
  tooltip?: string;
  popupClassName?: string;
  sectionNameClassName?: string;
  itemClassName?: string;
  dropDownArrowClassName?: string;
  dropDownArrowComponent?: React.ReactNode;
  searchTextfieldProps?: SearchTextFieldProps;
  searchTextFieldInputProps?: SearchTextFieldInputProps;
}

export const Selector: React.FC<SelectorProps> = ({
  label,
  name,
  popUpKey,
  error,
  choiceSections,
  placeholder,
  style,
  className,
  selectDivPropsStyle,
  selectDivClassName,
  disable,
  id,
  disablePortal,
  itemHeight,
  scrollDivHeight,
  tooltip,
  popupClassName,
  itemClassName,
  sectionNameClassName,
  dropDownArrowClassName,
  dropDownArrowComponent,
  searchTextfieldProps,
  searchTextFieldInputProps,
  handleSelect,
}) => {
  const [open, setOpen] = useState<boolean>(false);
  const selectFieldRef = useRef<HTMLDivElement>(null);

  const handleClosePopup = useCallback(() => {
    setOpen(false);
  }, []);

  const handleSelectChoice = (value: Choice) => {
    handleClosePopup();
    handleSelect({ value, name: name ?? '' });
  };

  return (
    <div ref={selectFieldRef} style={{ width: '100%', display: 'flex', ...style }} className={className || ''}>
      <SelectButton
        id={id}
        label={label}
        setOpen={setOpen}
        dropDownArrowClassName={dropDownArrowClassName}
        dropDownArrowComponent={dropDownArrowComponent}
        tooltip={tooltip}
        selectDivClassName={selectDivClassName}
        disable={disable}
        placeholder={placeholder}
        selectDivPropsStyle={selectDivPropsStyle}
        open={open}
        error={error}
      />
      {open && selectFieldRef.current && (
        <SelectorPopup
          handleSelect={handleSelectChoice}
          choiceSections={choiceSections}
          anchorEl={selectFieldRef.current}
          disablePortal={disablePortal}
          popUpKey={popUpKey}
          itemHeight={itemHeight}
          scrollDivHeight={scrollDivHeight}
          handleClose={handleClosePopup}
          className={popupClassName || ''}
          itemClassName={itemClassName}
          searchTextfieldProps={searchTextfieldProps}
          sectionNameClassName={sectionNameClassName}
          searchTextFieldInputProps={searchTextFieldInputProps}
          id={id}
        />
      )}
    </div>
  );
};

export type { Choice, ChoiceSection };
