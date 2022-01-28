import React, { useState, useRef, ChangeEvent } from 'react';
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
import ClickAwayListener from '@material-ui/core/ClickAwayListener';
import { DEFAULT_SCROLL_DIV_HEIGHT, DEFAULT_ITEM_HEIGHT } from '../const';
import MultipleSectionItem, { MultipleChoiceSection, MultipleChoice } from './MultipleSectionItem';

export type SearchTextFieldInputProps = Partial<InputProps> | Partial<FilledInputProps> | Partial<OutlinedInputProps>;
export type SearchTextFieldProps = TextFieldProps;

export interface Props {
  name: string;
  chosenChoice: { [key: string]: MultipleChoice | null };
  popUpKey: string;
  anchorEl: HTMLDivElement;
  choiceSections: MultipleChoiceSection[];
  id?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  className?: string;
  itemClassName?: string;
  sectionNameClassName?: string;
  searchTextFieldProps?: SearchTextFieldProps;
  searchTextFieldInputProps?: SearchTextFieldInputProps;
  handleClose: (chosenChoice: { [key: string]: MultipleChoice | null }) => void;
  handleSelect: (value: MultipleChoice, isCheck: boolean) => void;
  handleClearAll: () => void;
}

const MultipleSelectorPopup: React.FC<Props> = ({
  name,
  chosenChoice,
  popUpKey,
  anchorEl,
  choiceSections,
  id,
  itemHeight = DEFAULT_ITEM_HEIGHT,
  scrollDivHeight = DEFAULT_SCROLL_DIV_HEIGHT,
  className,
  itemClassName,
  sectionNameClassName,
  searchTextFieldProps,
  searchTextFieldInputProps,
  handleClose,
  handleSelect,
  handleClearAll,
}) => {
  const popupRef = useRef<HTMLDivElement>(null);
  const [searchWord, setSearchWord] = useState<string>('');
  const debouncedSearchWord = useDebounce(searchWord, 100);

  const handleSeaching = (e: ChangeEvent<HTMLTextAreaElement | HTMLInputElement>) => {
    setSearchWord(e.target.value);
  };

  const selectedChoicesLength = Object.values(chosenChoice).filter((value) => Boolean(value)).length;

  const filterChoices = (section: MultipleChoiceSection, searchString: string) => {
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

  const choices = choiceSections.reduce((acc, section: MultipleChoiceSection) => {
    const filteredSection = filterChoices(section, debouncedSearchWord);
    return filteredSection ? [...acc, ...filteredSection] : acc;
  }, []);

  const listHeight = choices.length * itemHeight > scrollDivHeight ? scrollDivHeight : choices.length * itemHeight;

  return (
    <Popover
      key={`popper-${popUpKey}`}
      open
      anchorEl={anchorEl}
      anchorOrigin={{
        vertical: 'bottom',
        horizontal: 'center',
      }}
      transformOrigin={{
        vertical: 'top',
        horizontal: 'center',
      }}
      ref={popupRef}
      PaperProps={{
        style: {
          backgroundColor: 'transparent',
          boxShadow: 'none',
        },
      }}
    >
      <ClickAwayListener
        onClickAway={() => {
          handleClose(chosenChoice);
        }}
      >
        <div className="px-4 py-1">
          <div className={`bg-white shadow-xl ${className}`}>
            <TextField
              fullWidth
              placeholder="Search"
              InputProps={{
                className: 'border-b px-4 py-1 placeholder-italic w-full',
                disableUnderline: true,
                endAdornment: (
                  <InputAdornment position="start">
                    <SearchIcon style={{ fontSize: '18px', marginLeft: '5px' }} />
                  </InputAdornment>
                ),
                ...searchTextFieldInputProps,
              }}
              onChange={handleSeaching}
              id={`${id}-seach-textfield`}
              autoComplete="off"
              autoFocus
              {...searchTextFieldProps}
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
                      <MultipleSectionItem
                        key={`item-${index + 1}`}
                        choice={choice}
                        checked={Boolean(
                          chosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice?.id ?? choice.label}`],
                        )}
                        handleSelect={handleSelect}
                        className={itemClassName}
                        id={id}
                      />
                    )}
                  </div>
                );
              }}
            </List>
          </div>
          <div
            className="bg-black flex flex-row min-w-max py-2 px-4 rounded mt-2"
            style={{ opacity: selectedChoicesLength > 1 ? 0.9 : 0 }}
          >
            <Typography className="text-white">{`${selectedChoicesLength} ${name}s are selected`}</Typography>
            <Typography
              onClick={handleClearAll}
              id={`${id}-clear-button`}
              style={{
                color: 'red',
                marginLeft: 'auto',
                borderLeft: '2px solid white',
                cursor: 'pointer',
                paddingLeft: '0.5rem',
              }}
            >
              Clear All
            </Typography>
          </div>
        </div>
      </ClickAwayListener>
    </Popover>
  );
};

export default MultipleSelectorPopup;
