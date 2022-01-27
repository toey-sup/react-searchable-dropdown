import React, { useState, ChangeEvent } from 'react';
import { makeStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';
import Popover from '@material-ui/core/Popover';
import TextField, { TextFieldProps } from '@material-ui/core/TextField';
import { OutlinedInputProps } from '@material-ui/core/OutlinedInput';
import { FilledInputProps } from '@material-ui/core/FilledInput';
import { InputProps } from '@material-ui/core/Input';
import SearchIcon from '@material-ui/icons/Search';
import InputAdornment from '@material-ui/core/InputAdornment';
import useDebounce from '../useDebounce';
import List from '../ListWIthId';
import { DEFAULT_SCROLL_DIV_HEIGHT, DEFAULT_ITEM_HEIGHT } from '../const';
import SelectorItem, { Choice, ChoiceSection } from './SectionItem';

export type SearchTextFieldInputProps = Partial<InputProps> | Partial<FilledInputProps> | Partial<OutlinedInputProps>;
export type SearchTextFieldProps = TextFieldProps;

export interface Props {
  popUpKey: string;
  choiceSections: ChoiceSection[];
  anchorEl: HTMLDivElement;
  id?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  disablePortal?: boolean;
  className?: string;
  itemClassName?: string;
  sectionNameClassName?: string;
  searchTextfieldProps?: SearchTextFieldProps;
  searchTextFieldInputProps?: SearchTextFieldInputProps;
  handleClose: () => void;
  handleSelect: (value: Choice) => void;
}

const SelectorPopup: React.FC<Props> = ({
  popUpKey,
  anchorEl,
  choiceSections,
  id,
  disablePortal,
  itemHeight = DEFAULT_ITEM_HEIGHT,
  scrollDivHeight = DEFAULT_SCROLL_DIV_HEIGHT,
  className,
  itemClassName,
  sectionNameClassName,
  searchTextfieldProps,
  searchTextFieldInputProps,
  handleClose,
  handleSelect,
}) => {
  const [searchWord, setSearchWord] = useState<string>('');
  const debouncedSearchWord = useDebounce(searchWord, 100);

  const handleSeaching = (e: ChangeEvent<HTMLTextAreaElement | HTMLInputElement>) => {
    setSearchWord(e.target.value);
  };

  const filterChoices = (section: ChoiceSection, searchString: string) => {
    const sectionChoices = section.choices.reduce((acc, choice) => {
      if (
        new RegExp(`${searchString.replace(/\[|\]|\(|\)|\+|-|\*|\\|\?|\^|\$/g, (e) => `\\${e}`)}`, 'i').test(
          choice.label,
        )
      ) {
        return [...acc, { ...choice, sectionPrefix: section.sectionPrefix }];
      }
      return acc;
    }, []);
    if (sectionChoices.length > 0) {
      return [...(section.sectionName ? [`${section.sectionName} (${sectionChoices.length})`] : []), ...sectionChoices];
    }
    return null;
  };

  const choices = choiceSections.reduce((acc, section: ChoiceSection) => {
    const filteredSection = filterChoices(section, debouncedSearchWord);
    return filteredSection ? [...acc, ...filteredSection] : acc;
  }, []);

  const listHeight = choices.length * itemHeight > scrollDivHeight ? scrollDivHeight : choices.length * itemHeight;

  return (
    <Popover
      key={`popper-${popUpKey}`}
      id="rightClick-menu"
      open
      disablePortal={disablePortal}
      onClose={handleClose}
      anchorEl={anchorEl}
      anchorOrigin={{
        vertical: 'bottom',
        horizontal: 'center',
      }}
      transformOrigin={{
        vertical: 'top',
        horizontal: 'center',
      }}
      className={`${className}`}
    >
      <TextField
        fullWidth
        placeholder="Search"
        className={''}
        InputProps={{
          disableUnderline: true,
          className: 'border-b px-4 py-1 placeholder-italic',
          endAdornment: (
            <InputAdornment position="start">
              <SearchIcon style={{ fontSize: '18px' }} />
            </InputAdornment>
          ),
          ...searchTextFieldInputProps,
        }}
        onChange={handleSeaching}
        id={`${id}-seach-field`}
        autoComplete="off"
        {...searchTextfieldProps}
      />
      <List
        height={listHeight}
        itemCount={choices.length}
        itemSize={itemHeight}
        width={anchorEl?.clientWidth}
        overscanCount={10}
        outerId={`${id}-list-outer-div`}
        innerId={`${id}-list-inner-div`}
      >
        {({ index, style }) => {
          const choice = choices[index];
          return (
            <div id={`${id}-${index}-choice-div`} style={{ ...style, height: itemHeight }}>
              {typeof choice === 'string' ? (
                <Typography className={`flex items-center h-full px-4 bg-gray-100 ${sectionNameClassName}`}>
                  {choice}
                </Typography>
              ) : (
                <SelectorItem id={id} choice={choice} handleSelect={handleSelect} className={itemClassName} />
              )}
            </div>
          );
        }}
      </List>
    </Popover>
  );
};

export default SelectorPopup;
