import React, { useState, ChangeEvent } from 'react';
import { makeStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';
import Popover from '@material-ui/core/Popover';
import TextField from '@material-ui/core/TextField';
import SearchIcon from '@material-ui/icons/Search';
import InputAdornment from '@material-ui/core/InputAdornment';
import useDebounce from '../useDebounce';
import List from '../ListWIthId';
import { DEFAULT_SCROLL_DIV_HEIGHT, DEFAULT_ITEM_HEIGHT } from '../const';
import SelectorItem, { ChoiceSections } from './SectionItem';


const useStyles = makeStyles({
  popUp: (props: { selectDivWidth: number }) => ({
    zIndex: 9999,
    '& .MuiPaper-root': {
      width: props.selectDivWidth,
      zIndex: 11,
      backgroundColor: 'white',
      height: 'fit-content',
      display: 'flex',
      flexFlow: 'wrap column',
      borderRadius: 4,
      boxShadow:
          '0 4px 8px 0 rgba(0, 0, 0, 0.2), 0 6px 20px 0 rgba(0, 0, 0, 0.19)',
    },
  }),
  searchDiv: {
    '& .MuiInput-input': {
      padding: '9px 15px',
    },
  },
  input: {
    '&::placeholder': {
      fontStyle: 'italic',
    },
  },
  sectionName: {
    display: 'flex',
    alignItems: 'center',
    textAlign: 'left',
    height: '100%',
    padding: '0px 16px',
    backgroundColor: '#F7F7F7',
    borderTop: '1px solid #F3F3F3',
    borderBottom: '1px solid #F3F3F3',
  },
});

export interface Props {
  popUpKey: string;
  choiceSections: ChoiceSections[];
  anchorEl: HTMLDivElement;
  id?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  disablePortal?: boolean;
  handleClose: () => void;
  handleSelect: (value: { [key: string]: any }) => void;
}

const SelectorPopup: React.FC<Props> = ({
  popUpKey,
  anchorEl,
  choiceSections,
  id,
  disablePortal,
  itemHeight = DEFAULT_ITEM_HEIGHT,
  scrollDivHeight = DEFAULT_SCROLL_DIV_HEIGHT,
  handleClose,
  handleSelect,
}) => {
  const classes = useStyles({ selectDivWidth: anchorEl?.clientWidth });
  const [searchWord, setSearchWord] = useState<string>('');
  const debouncedSearchWord = useDebounce(searchWord, 100);

  const handleSeaching = (e: ChangeEvent<HTMLTextAreaElement | HTMLInputElement>) => {
    setSearchWord(e.target.value);
  };

  const filterChoices = (section: ChoiceSections, searchString: string) => {
    const sectionChoices = section.choices.reduce((acc, choice) => {
      if (new RegExp(`${searchString.replace(/\[|\]|\(|\)|\+|-|\*|\\|\?|\^|\$/g, (e) => (`\\${e}`))}`, 'i').test(choice.label)) {
        return [...acc, { ...choice, sectionPrefix: section.sectionPrefix }];
      }
      return acc;
    }, []);
    if (sectionChoices.length > 0) {
      return [...section.sectionName ? [`${section.sectionName} (${sectionChoices.length})`] : [], ...sectionChoices];
    }
    return null;
  };

  const choices = choiceSections
    .reduce((acc, section: ChoiceSections) => {
      const filteredSection = filterChoices(section, debouncedSearchWord);
      return filteredSection ? [...acc, ...filteredSection] : acc;
    }, []);

  const listHeight = (choices.length * itemHeight) > scrollDivHeight
    ? scrollDivHeight : choices.length * itemHeight;

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
      className={classes.popUp}
    >
      <TextField
        fullWidth
        placeholder="Search"
        className={classes.searchDiv}
        InputProps={{
          disableUnderline: true,
          classes: { input: classes.input },
          endAdornment: <InputAdornment position="start"><SearchIcon style={{ fontSize: '18px' }} /></InputAdornment>,
        }}
        onChange={handleSeaching}
        id={`${id}-seach-field`}
        autoComplete="off"
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
            {(typeof choice === 'string')
              ? <Typography className={classes.sectionName}>{choice}</Typography>
              : (
                <SelectorItem id={id} choice={choice} handleSelect={handleSelect} />
              )}
          </div>
        )}}
      </List>
    </Popover>
  );
};

export default SelectorPopup;
