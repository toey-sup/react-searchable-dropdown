import React, { useState, useCallback, useRef } from 'react';
import { makeStyles } from '@material-ui/core/styles';
import Tooltip from '@material-ui/core/Tooltip';
import Typography from '@material-ui/core/Typography';
import ExpandMoreIcon from '@material-ui/icons/ExpandMore';
import SelectorPopup from './SelectorPopup';
import { ChoiceSections, Choice } from './SectionItem';

const useStyles = makeStyles({
  selectDiv: {
    alignItems: 'center',
    display: 'flex',
    width: '100%',
    border: `1px solid #E6E6E6`,
    borderRadius: '4px',
    minWidth: '170px',
    height: '35px',
    position: 'relative',
    padding: '0px 15px',
    '&:hover': {
      border: `1px solid #919191 !important`,
    },
    backgroundColor: 'white',
    outline: 'none !important',
    outlineOffset: 'none !important',
  },
  disabled: {
    pointerEvents: 'none',
    background: '#E6E6E6',
    border: '1px solid #424242 important',
    '& svg': {
      color: '#828282',
    },
    '& p': {
      opacity: 0.35,
    },
  },
  openSelect: {
    border: '1px solid #919191 !important',
  },
  textContainer: {
    width: '100%',
    display: 'flex',
    overflow: 'hidden',
  },
  label: {
    maxWidth: '100%',
  },
  labelPrefix: {
    color: '#63B178',
    width: 'fit-content',
    minWidth: 'fit-content',
    whiteSpace: 'break-spaces',
    fontStyle: 'italic',
    userSelect: 'none',
  },
  expandIcon: {
    display: 'flex',
    padding: '1px',
    right: '0',
    marginLeft: 'auto',
  },
  errorDiv: {
    border: '1px solid #D64646 !important',
  },
  placeholder: {
    whiteSpace: 'nowrap',
    color: '#919191',
    opacity: 0.75,
    fontStyle: 'italic',
    fontWeight: 400,
    overflow: 'hidden',
  },
});

export interface Props {
  label: string;
  popUpKey: string;
  choiceSections: ChoiceSections[];
  selectDivPropsStyle?: { [key:string]: any};
  style?: { [key:string]: any};
  className?: any,
  handleSelect: ({ value, name }: { value: Choice, name: string }) => void;
  labelPrefix?: string;
  name?: string;
  error?: boolean;
  placeholder?: string;
  disable?:boolean;
  id?: string;
  disablePortal?: boolean;
  itemHeight?: number;
  scrollDivHeight?: number;
  tooltip?: string;
  topDivClassName?: string;
  popupClassName?: string;
  itemClassName?: string;
  disableDropDownArrow?: boolean;
  dropDownArrowClassName?: string;
}

const Selector: React.FC<Props> = ({
  label,
  labelPrefix,
  name,
  popUpKey,
  error,
  choiceSections,
  placeholder,
  selectDivPropsStyle,
  className,
  style,
  disable,
  id,
  disablePortal,
  itemHeight,
  scrollDivHeight,
  tooltip,
  topDivClassName,
  popupClassName,
  itemClassName,
  disableDropDownArrow,
  dropDownArrowClassName,
  handleSelect,
}) => {
  const classes = useStyles();
  const [open, setOpen] = useState<boolean>(false);
  const selectFieldRef = useRef<HTMLDivElement>(null);

  const handleClosePopup = useCallback(() => { setOpen(false); }, []);

  const handleSelectChoice = (value: Choice) => {
    handleClosePopup();
    handleSelect({ value, name: name ?? '' });
  };

  return (
    <div ref={selectFieldRef} style={{ width: '100%', display: 'flex', ...style }} className={topDivClassName}>
      <Tooltip
        title={tooltip ?? `${label ? `${labelPrefix || ''} ${label}` : ''}`}
        key={tooltip ?? `${labelPrefix || ''} ${label}`}
        enterDelay={800}
        enterNextDelay={500}
        interactive
        placement="top"
        arrow
      >
        <button
          type="button"
          className={`
          ${classes.selectDiv}
          ${open ? classes.openSelect : ''}
          ${error ? classes.errorDiv : ''}
          ${disable ? classes.disabled : ''}
          ${className}
        `}
          style={selectDivPropsStyle}
          onClick={() => setOpen(true)}
          id={`${id}-select-button`}
        >
          <div className={classes.textContainer}>
            {((label) && !disable && labelPrefix) && (
            <Typography variant="body1" className={classes.labelPrefix} noWrap>
              {labelPrefix}
            </Typography>
            )}
            {((!label) && !disable)
              ? (
                <Typography variant="body1" className={classes.placeholder}>
                  {placeholder}
                </Typography>
              )
              : (
                <Typography variant="body1" className={classes.label} noWrap>
                  {label}
                </Typography>
              )}
          </div>
          {!disableDropDownArrow && <div className={`${classes.expandIcon} ${dropDownArrowClassName}`}>
            <ExpandMoreIcon style={{ fontSize: '15px' }} />
          </div>}
        </button>
      </Tooltip>
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
        className={popupClassName}
        itemClassName={itemClassName}
        id={id}
      />
      )}
    </div>
  );
};

export type { Choice, ChoiceSections };
export default Selector;
