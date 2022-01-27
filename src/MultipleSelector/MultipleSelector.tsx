/* eslint-disable jsx-a11y/no-static-element-interactions */
import React, { useState, useCallback, useRef, useEffect } from 'react';
import { MultipleChoiceSection, MultipleChoice } from './MultipleSectionItem';
import MultipleSelectorPopup, { SearchTextFieldProps, SearchTextFieldInputProps } from './MultipleSelectorPopup';
import SelectButton from '../SelectButton';

export interface MultipleSelectorProps {
  label: string;
  popUpKey: string;
  choiceSections: MultipleChoiceSection[];
  name?: string;
  error?: boolean;
  placeholder?: string;
  disable?: boolean;
  checkedChoices?: MultipleChoice[];
  id?: string;
  style?: React.CSSProperties;
  className?: string;
  selectDivPropsStyle?: React.CSSProperties;
  selectDivClassName?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  popupClassName?: string;
  itemClassName?: string;
  sectionNameClassName?: string;
  dropDownArrowClassName?: string;
  dropDownArrowComponent?: HTMLElement;
  searchTextFieldProps?: SearchTextFieldProps;
  searchTextFieldInputProps?: SearchTextFieldInputProps;
  handleSelect: ({ value, name }: { value: MultipleChoice[]; name: string }) => void;
}

export const MultipleSelector: React.FC<MultipleSelectorProps> = ({
  label,
  name,
  popUpKey,
  error,
  choiceSections,
  placeholder,
  disable,
  checkedChoices,
  id,
  className,
  style,
  selectDivPropsStyle,
  selectDivClassName,
  itemHeight,
  scrollDivHeight,
  popupClassName,
  itemClassName,
  sectionNameClassName,
  dropDownArrowClassName,
  searchTextFieldProps,
  dropDownArrowComponent,
  searchTextFieldInputProps,
  handleSelect,
}) => {
  const [open, setOpen] = useState<boolean>(false);
  const [chosenChoice, setChosenChoice] = useState<{ [key: string]: MultipleChoice | null }>({});
  const [mulChoiceSections, setMulChoiceSections] = useState<MultipleChoiceSection[]>([...choiceSections]);
  const selectFieldRef = useRef<HTMLDivElement>(null);

  const handleClosePopup = useCallback(
    (submitChoices: { [key: string]: MultipleChoice | null }) => {
      setOpen(false);
      if (submitChoices) {
        let selectedChoice = Object.keys(submitChoices).reduce((acc, choiceLabel) => {
          const choice = submitChoices[choiceLabel];
          return choice ? [...acc, choice] : acc;
        }, []);
        // handle if previously user select single choice
        // and user not selecting new choices
        if (
          Object.keys(submitChoices).length === 0 &&
          checkedChoices &&
          checkedChoices[0] &&
          checkedChoices[0].singleChoice
        ) {
          selectedChoice = [checkedChoices[0]];
        }
        handleSelect({ value: selectedChoice, name: name ?? '' });
      }
    },
    [checkedChoices, handleSelect, name],
  );

  const handleSelectChoice = (value: MultipleChoice, isCheck: boolean) => {
    setChosenChoice({ ...chosenChoice, [`${value.id ?? value.label}`]: isCheck || value.singleChoice ? value : null });
    if (value.singleChoice) {
      handleClosePopup({
        [`${value.singleChoice ? 'Single -' : ''}${value.id ?? value.label}`]:
          isCheck || value.singleChoice ? value : null,
      });
    }
  };

  const handleClearAll = () => {
    setChosenChoice({});
  };

  useEffect(() => {
    const initChosenChoice: { [key: string]: MultipleChoice } = {};
    if (checkedChoices && checkedChoices[0] && !checkedChoices[0].singleChoice) {
      checkedChoices.forEach((choice) => {
        if (choice.label.trim().length > 0) {
          initChosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice.id ?? choice.label}`] = choice;
        }
      });
    }
    setChosenChoice(initChosenChoice);
    setMulChoiceSections(
      choiceSections.map((section) => ({
        ...section,
        choices: section.choices.map((choice) => ({
          ...choice,
          checked: Boolean(initChosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice.id ?? choice.label}`]),
        })),
      })),
    );
  }, [checkedChoices, choiceSections]);

  const tooltipLabel = checkedChoices ? checkedChoices?.map((choice) => choice.label).join(', ') : '';

  return (
    <div ref={selectFieldRef} style={{ width: '100%', display: 'flex', ...style }} className={className}>
      <SelectButton
        id={id}
        label={label}
        setOpen={setOpen}
        dropDownArrowClassName={dropDownArrowClassName}
        dropDownArrowComponent={dropDownArrowComponent}
        tooltip={tooltipLabel}
        selectDivClassName={selectDivClassName}
        disable={disable}
        placeholder={placeholder}
        selectDivPropsStyle={selectDivPropsStyle}
        open={open}
        error={error}
      />
      {open && selectFieldRef.current && (
        <MultipleSelectorPopup
          choiceSections={mulChoiceSections}
          anchorEl={selectFieldRef.current}
          popUpKey={popUpKey}
          name={name ?? ''}
          chosenChoice={chosenChoice}
          id={id}
          itemHeight={itemHeight}
          scrollDivHeight={scrollDivHeight}
          handleSelect={handleSelectChoice}
          handleClose={handleClosePopup}
          handleClearAll={handleClearAll}
          className={popupClassName}
          itemClassName={itemClassName}
          sectionNameClassName={sectionNameClassName}
          searchTextFieldProps={searchTextFieldProps}
          searchTextFieldInputProps={searchTextFieldInputProps}
        />
      )}
    </div>
  );
};

export type { MultipleChoiceSection, MultipleChoice, SearchTextFieldProps, SearchTextFieldInputProps };
